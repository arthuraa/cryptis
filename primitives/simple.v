From cryptis Require Import lib.
From mathcomp Require Import ssreflect.
From mathcomp Require order.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap reservation_map.
From iris.base_logic.lib Require Import invariants saved_prop.
From iris.program_logic Require Import atomic.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import nondet_bool.
From cryptis Require Import term.
From cryptis.primitives Require Import notations pre_term comp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition tint : val := λ: "n",
  (#TInt_tag, "n").

Definition to_int : val := λ: "t",
  if: Fst "t" = #TInt_tag then SOME (Snd "t")
  else NONE.

Definition tuple : val := λ: "t1" "t2",
  (#TPair_tag, ("t1", "t2")).

Definition untuple : val := λ: "t",
  if: Fst "t" = #TPair_tag then SOME (Snd "t")
  else NONE.

Definition list_of_term : val := rec: "loop" "t" :=
  if: Fst "t" = #TInt_tag then
    if: Snd "t" = #0 then SOMEV NONEV else NONEV
  else if: Fst "t" = #TPair_tag then
    let: "t" := Snd "t" in
    bind: "l" := "loop" (Snd "t") in
    SOME (SOME (Fst "t", "l"))
  else NONE.

Definition term_of_list : val := rec: "loop" "l" :=
  match: "l" with NONE => (#TInt_tag, #0)
  | SOME "p" => tuple (Fst "p") ("loop" (Snd "p"))
  end.

Definition tag : val := λ: "N" "t",
  tuple "N" "t".

Definition untag : val := λ: "N" "t",
  bind: "t" := untuple "t" in
  let: "N'" := (Fst "t") in
  if: eq_term "N" "N'" then SOME (Snd "t") else NONE.

Definition is_key : val := λ: "t",
  if: Fst "t" = #TKey_tag then SOME (Fst (Snd "t"))
  else NONE.

Definition seal : val := λ: "k" "t", (#TSeal_tag, ("k", "t")).

Definition hash : val := λ: "t", (#THash_tag, "t").

Definition key kt : val := λ: "k",
  (#TKey_tag, (#(int_of_key_type kt), "k")).

Definition open : val := λ: "k" "t",
  if: (Fst "k" = #TKey_tag)
      && (Fst (Snd "k") = #(int_of_key_type Open))
      && (Fst "t" = #TSeal_tag)
      && (eq_term (key Seal (Snd (Snd "k"))) (Fst (Snd "t"))) then
    SOME (Snd (Snd "t"))
  else
    NONE.

Definition enc : val := λ: "k" "N" "t",
  seal "k" (tag "N" "t").

Definition dec : val := λ: "k" "N" "t",
  bind: "t" := open "k" "t" in
  untag "N" "t".

Definition mk_keys : val := λ: "k",
  (key Seal "k", key Open "k").

Definition derive_key : val := λ: "k",
  tag (Tag $ nroot.@"keys".@"sym") "k".

Definition pkey : val := λ: "sk", key Seal "sk".

Definition aenc : val := λ: "pk" "N" "t",
  enc "pk" "N" "t".

Definition adec : val := λ: "sk" "N" "t",
  dec (key Open "sk") "N" "t".

Definition senc : val := λ: "sk" "N" "t",
  enc (key Seal "sk") "N" "t".

Definition sdec : val := λ: "sk" "N" "t",
  dec (key Open "sk") "N" "t".

Definition vkey : val := λ: "sk", key Open "sk".

Definition sign : val := λ: "sk" "N" "t",
  enc (key Seal "sk") "N" "t".

Definition verify : val := λ: "vk" "N" "t",
  dec "vk" "N" "t".

Definition to_seal_key : val := λ: "t",
  bind: "kt" := is_key "t" in
  guard: ("kt" = repr Seal) in
  SOME "t".

Definition to_open_key : val := λ: "t",
  bind: "kt" := is_key "t" in
  guard: ("kt" = repr Open) in
  SOME "t".

Section Proofs.

Context `{!heapGS Σ}.
Notation nonce := loc.

Implicit Types E : coPset.
Implicit Types a : nonce.
Implicit Types t : term.
Implicit Types v : val.
Implicit Types Φ : prodO locO termO -n> iPropO Σ.
Implicit Types Ψ : val → iProp Σ.

Lemma twp_tint E Ψ n : Ψ (TInt n) ⊢ WP tint #n @ E [{ Ψ }].
Proof.
by rewrite /tint val_of_term_unseal; iIntros "Hpost"; wp_pures.
Qed.

Lemma wp_tint E Ψ n : Ψ (TInt n) ⊢ WP tint #n @ E {{ Ψ }}.
Proof. by iIntros "?"; iApply twp_wp; iApply twp_tint. Qed.

Lemma twp_to_int E t Ψ :
  Ψ (repr (Spec.to_int t)) ⊢
  WP to_int t @ E [{ Ψ }].
Proof.
rewrite /to_int val_of_term_unseal; iIntros "Hpost"; wp_pures.
case: t; by move=> *; wp_pures; eauto.
Qed.

Lemma wp_to_int E t Ψ :
  Ψ (repr (Spec.to_int t)) ⊢
  WP to_int t @ E {{ Ψ }}.
Proof.
by iIntros "?"; iApply twp_wp; iApply twp_to_int.
Qed.

Lemma twp_tuple E t1 t2 Ψ :
  Ψ (TPair t1 t2) ⊢
  WP tuple t1 t2 @ E [{ Ψ }].
Proof.
rewrite val_of_term_unseal /tuple; by iIntros "?"; wp_pures.
Qed.

Lemma wp_tuple E t1 t2 Ψ :
  Ψ (TPair t1 t2) ⊢
  WP tuple t1 t2 @ E {{ Ψ }}.
Proof.
by iIntros "?"; iApply twp_wp; iApply twp_tuple.
Qed.

Lemma twp_untuple E t Ψ :
  Ψ (repr (Spec.untuple t)) ⊢
  WP untuple t @ E [{ Ψ }].
Proof.
iIntros "post".
rewrite /Spec.untuple /untuple /= val_of_term_unseal.
case: t; by move=> *; wp_pures; iApply "post".
Qed.

Lemma wp_untuple E t Ψ :
  Ψ (repr (Spec.untuple t)) ⊢
  WP untuple t @ E {{ Ψ }}.
Proof.
by iIntros "?"; iApply twp_wp; iApply twp_untuple.
Qed.

Lemma twp_term_of_list E ts Ψ :
  Ψ (repr (Spec.of_list ts)) ⊢
  WP term_of_list (repr ts) @ E [{ Ψ }].
Proof.
rewrite /= [in repr_list ts]repr_list_unseal Spec.of_list_unseal.
elim: ts Ψ => [|t ts IH] Ψ /=; iIntros "post"; wp_rec; wp_pures.
  by rewrite val_of_term_unseal.
wp_bind (term_of_list _); iApply IH; wp_pures.
by iApply twp_tuple.
Qed.

Lemma wp_term_of_list E ts Ψ :
  Ψ (repr (Spec.of_list ts)) ⊢
  WP term_of_list (repr ts) @ E {{ Ψ }}.
Proof.
by iIntros "?"; iApply twp_wp; iApply twp_term_of_list.
Qed.

Lemma twp_list_of_term E t Ψ :
  Ψ (repr (Spec.to_list t)) ⊢
  WP list_of_term t @ E [{ Ψ }].
Proof.
rewrite val_of_term_unseal /= repr_list_unseal.
elim/term_ind': t Ψ;
try by move=> *; iIntros "post"; wp_rec; wp_pures; iApply "post".
  move=> n Ψ /=; iIntros "post"; wp_rec; wp_pures.
  case: bool_decide_reflect => [[->]|]; first by wp_pures.
  case: n => *; by wp_pures.
move=> thead _ trest IH Ψ /=; iIntros "post".
wp_rec; wp_pures; wp_bind (list_of_term _); iApply IH.
case: (Spec.to_list trest) => [ts|] /=; wp_pures; eauto.
by rewrite -val_of_term_unseal.
Qed.

Lemma wp_list_of_term E t Ψ :
  Ψ (repr (Spec.to_list t)) ⊢
  WP list_of_term t @ E {{ Ψ }}.
Proof.
by iIntros "?"; iApply twp_wp; iApply twp_list_of_term.
Qed.

Lemma twp_list `{!Repr A} (xs : list A) E Ψ :
  Ψ (repr xs) ⊢
  WP list_to_expr xs @ E [{ Ψ }].
Proof.
elim: xs Ψ => [|x xs IH] /= Ψ; iIntros "post".
  by iApply (@twp_nil A _).
wp_bind (list_to_expr _); iApply IH.
by iApply (@twp_cons A).
Qed.

Lemma wp_list `{!Repr A} (xs : list A) E Ψ :
  Ψ (repr xs) ⊢
  WP list_to_expr xs @ E {{ Ψ }}.
Proof. by iIntros "?"; iApply twp_wp; iApply twp_list. Qed.

Lemma twp_tag E N t Ψ :
  Ψ (repr (Spec.tag N t)) ⊢
  WP tag N t @ E [{ Ψ }].
Proof.
iIntros "post".
by rewrite Spec.tag_unseal /tag; wp_pures; iApply twp_tuple.
Qed.

Lemma wp_tag E N t Ψ :
  Ψ (repr (Spec.tag N t)) ⊢
  WP tag N t @ E {{ Ψ }}.
Proof.
iIntros "post".
by rewrite Spec.tag_unseal /tag; wp_pures; iApply wp_tuple.
Qed.

Lemma twp_untag E N t Ψ :
  Ψ (repr (Spec.untag N t)) ⊢
  WP untag N t @ E [{ Ψ }].
Proof.
iIntros "post".
rewrite Spec.untag_unseal /untag /=; wp_pures.
wp_bind (untuple _); iApply twp_untuple.
case: t; try by [move=> *; wp_pures; iApply "post"].
move=> t1 t2; wp_pures.
wp_apply twp_eq_term.
rewrite bool_decide_decide.
by case: decide => [<-|ne]; wp_pures => //.
Qed.

Lemma wp_untag E N t Ψ :
  Ψ (repr (Spec.untag N t)) ⊢
  WP untag N t @ E {{ Ψ }}.
Proof.
by iIntros "?"; iApply twp_wp; iApply twp_untag.
Qed.

Lemma twp_key kt E (k : term) ψ :
  ψ (TKey kt k : val) ⊢
  WP key kt k @ E [{ ψ }].
Proof.
rewrite val_of_term_unseal /=.
by iIntros "post"; wp_lam; wp_pures.
Qed.

Lemma wp_key kt E (k : term) ψ :
  ψ (TKey kt k : val) ⊢
  WP key kt k @ E {{ ψ }}.
Proof.
rewrite val_of_term_unseal /=.
by iIntros "post"; wp_lam; wp_pures.
Qed.

Lemma twp_mk_keys E (k : term) Ψ :
  Ψ (TKey Seal k, TKey Open k)%V ⊢
  WP mk_keys k @ E [{ Ψ }].
Proof.
rewrite /mk_keys.
iIntros "post"; wp_pures.
wp_apply twp_key.
wp_apply twp_key.
by wp_pures.
Qed.

Lemma wp_mk_keys E (k : term) Ψ :
  Ψ (TKey Seal k, TKey Open k)%V ⊢
  WP mk_keys k @ E {{ Ψ }}.
Proof.
by iIntros "post"; iApply twp_wp; iApply twp_mk_keys.
Qed.

Lemma twp_derive_key E (k : term) Ψ :
  Ψ (Spec.derive_key k) ⊢
  WP derive_key k @ E [{ Ψ }].
Proof.
rewrite /derive_key. iIntros "post". wp_pures.
wp_pures. by wp_apply twp_tag.
Qed.

Lemma wp_derive_key E (k : term) Ψ :
  Ψ (Spec.derive_key k) ⊢
  WP derive_key k @ E {{ Ψ }}.
Proof.
by iIntros "post"; iApply twp_wp; iApply twp_derive_key.
Qed.

Lemma twp_seal E t1 t2 Ψ :
  Ψ (TSeal t1 t2) ⊢
  WP seal t1 t2 @ E [{ Ψ }].
Proof.
rewrite !val_of_term_unseal /seal.
iIntros "H".
case: t1; try by move=> *; wp_pures; eauto.
Qed.

Lemma wp_seal E t1 t2 Ψ :
  Ψ (TSeal t1 t2) ⊢
  WP seal  t1 t2 @ E {{ Ψ }}.
Proof. by iIntros "?"; iApply twp_wp; iApply twp_seal. Qed.

Lemma twp_hash E t Ψ : Ψ (THash t) ⊢ WP hash t @ E [{ Ψ }].
Proof.
by rewrite /hash val_of_term_unseal; iIntros "?"; wp_pures.
Qed.

Lemma wp_hash E t Ψ : Ψ (THash t) ⊢ WP hash t @ E {{ Ψ }}.
Proof. by iIntros "?"; iApply twp_wp; iApply twp_hash. Qed.

Lemma twp_open E t1 t2 Ψ :
  Ψ (repr (Spec.open t1 t2)) ⊢
  WP open t1 t2 @ E [{ Ψ }].
Proof.
rewrite /repr /repr_option /repr /repr_term !val_of_term_unseal /open.
iIntros "H".
wp_pures.
case: t1; try by move=> /= *; wp_pures.
case; try by move=> /= *; wp_pures.
move=> tk; wp_pures.
case: t2; try by move=> /= *; wp_pures.
move=> tk' t /=; wp_pures.
rewrite -val_of_term_unseal.
wp_pures.
wp_apply twp_key. wp_apply twp_eq_term.
case: tk' => //=; try by move=> *; wp_pures.
case=> [] tk' //= *; wp_pures => //.
rewrite bool_decide_decide; case: decide => [<-|ne].
- by rewrite decide_True //; wp_pures.
- by rewrite decide_False; last congruence; wp_pures.
Qed.

Lemma wp_open E t1 t2 Ψ :
  Ψ (repr (Spec.open t1 t2)) ⊢
  WP open t1 t2 @ E {{ Ψ }}.
Proof. by iIntros "?"; iApply twp_wp; iApply twp_open. Qed.

Lemma twp_enc E k N t Ψ :
  Ψ (Spec.enc k N t) ⊢
  WP enc k N t @ E [{ Ψ }].
Proof.
iIntros "post"; rewrite /enc; wp_pures.
wp_bind (tag _ _); iApply twp_tag.
by iApply twp_seal.
Qed.

Lemma wp_enc E k N t Ψ :
  Ψ (Spec.enc k N t) ⊢
  WP enc k N t @ E {{ Ψ }}.
Proof. by iIntros "?"; iApply twp_wp; iApply twp_enc. Qed.

Lemma twp_dec E k N t Ψ :
  Ψ (repr (Spec.dec k N t)) ⊢
  WP dec k N t @ E [{ Ψ }].
Proof.
iIntros "post"; rewrite /dec; wp_pures.
wp_bind (open _ _); iApply twp_open.
rewrite /Spec.dec.
case e: (Spec.open _ _) => [t'|]; wp_pures => //.
by iApply twp_untag.
Qed.

Lemma wp_dec E k N t Ψ :
  Ψ (repr (Spec.dec k N t)) ⊢
  WP dec k N t @ E {{ Ψ }}.
Proof. by iIntros "?"; iApply twp_wp; iApply twp_dec. Qed.

Lemma twp_aenc pk N t Ψ :
  Ψ (Spec.enc pk N t) ⊢
  WP aenc pk N t [{ Ψ }].
Proof. iIntros "?". wp_lam. wp_pures. by wp_apply twp_enc. Qed.

Lemma wp_aenc pk N t Ψ :
  Ψ (Spec.enc pk N t) ⊢
  WP aenc pk N t {{ Ψ }}.
Proof. iIntros "?". wp_lam. wp_pures. by wp_apply wp_enc. Qed.

Lemma twp_adec k N t Ψ :
  Ψ (repr (Spec.dec (TKey Open k) N t)) ⊢
  WP adec k N t [{ Ψ }].
Proof.
iIntros "?". wp_lam; wp_pures.
wp_apply twp_key. by wp_apply twp_dec.
Qed.

Lemma wp_adec k N t Ψ :
  Ψ (repr (Spec.dec (TKey Open k) N t)) ⊢
  WP adec k N t {{ Ψ }}.
Proof.
iIntros "?". wp_lam; wp_pures.
wp_apply wp_key. by wp_apply wp_dec.
Qed.

Lemma twp_pkey k Ψ : Ψ (TKey Seal k) ⊢ WP pkey k [{ Ψ }].
Proof. iIntros "?". wp_lam; wp_pures. by wp_apply twp_key. Qed.

Lemma wp_pkey k Ψ : Ψ (TKey Seal k) ⊢ WP pkey k {{ Ψ }}.
Proof. iIntros "?". wp_lam; wp_pures. by wp_apply wp_key. Qed.

Lemma twp_senc E k N t Ψ :
  Ψ (Spec.enc (TKey Seal k) N t) ⊢
  WP senc k N t @ E [{ Ψ }].
Proof.
iIntros "post"; rewrite /senc /Spec.enc; wp_pures.
wp_apply twp_key. by wp_apply twp_enc.
Qed.

Lemma wp_senc E k N t Ψ :
  Ψ (Spec.enc (TKey Seal k) N t) ⊢
  WP senc k N t @ E {{ Ψ }}.
Proof. by iIntros "?"; iApply twp_wp; iApply twp_senc. Qed.

Lemma twp_sdec E k N t Ψ :
  Ψ (repr (Spec.dec (TKey Open k) N t)) ⊢
  WP sdec k N t @ E [{ Ψ }].
Proof.
iIntros "post"; rewrite /sdec; wp_pures.
wp_apply twp_key. by wp_apply twp_dec.
Qed.

Lemma wp_sdec E k N t Ψ :
  Ψ (repr (Spec.dec (TKey Open k) N t)) ⊢
  WP sdec k N t @ E {{ Ψ }}.
Proof. by iIntros "?"; iApply twp_wp; iApply twp_sdec. Qed.

Lemma twp_sign k N t Ψ :
  Ψ (Spec.enc (TKey Seal k) N t) ⊢
  WP sign k N t [{ Ψ }].
Proof.
iIntros "?". wp_lam; wp_pures. wp_apply twp_key. by wp_apply twp_enc.
Qed.

Lemma wp_sign k N t Ψ :
  Ψ (Spec.enc (TKey Seal k) N t) ⊢
  WP sign k N t {{ Ψ }}.
Proof.
iIntros "?". wp_lam; wp_pures. wp_apply wp_key. by wp_apply wp_enc.
Qed.

Lemma twp_verify k N t Ψ :
  Ψ (repr (Spec.dec k N t)) ⊢
  WP verify k N t [{ Ψ }].
Proof.
iIntros "?". wp_lam; wp_pures. by wp_apply twp_dec.
Qed.

Lemma wp_verify k N t Ψ :
  Ψ (repr (Spec.dec k N t)) ⊢
  WP verify k N t {{ Ψ }}.
Proof.
iIntros "?". wp_lam; wp_pures. by wp_apply wp_dec.
Qed.

Lemma twp_vkey k Ψ : Ψ (TKey Open k) ⊢ WP vkey k [{ Ψ }].
Proof. iIntros "?". wp_lam; wp_pures. by wp_apply twp_key. Qed.

Lemma wp_vkey k Ψ : Ψ (TKey Open k) ⊢ WP vkey k {{ Ψ }}.
Proof. iIntros "?". wp_lam; wp_pures. by wp_apply wp_key. Qed.

Lemma twp_is_key E t Ψ :
  Ψ (repr (Spec.is_key t)) ⊢
  WP is_key t @ E [{ Ψ }].
Proof.
rewrite /repr /repr_option val_of_term_unseal /is_key.
iIntros "?"; by case: t=> *; wp_pures.
Qed.

Lemma wp_is_key E t Ψ :
  Ψ (repr (Spec.is_key t)) ⊢
  WP is_key t @ E {{ Ψ }}.
Proof. by iIntros "?"; iApply twp_wp; iApply twp_is_key. Qed.

Lemma wp_to_seal_key E t Ψ :
  Ψ (repr (Spec.to_seal_key t)) ⊢
  WP to_seal_key t @ E {{ Ψ }}.
Proof.
rewrite /to_seal_key; iIntros "post".
wp_pures; wp_bind (is_key _); iApply wp_is_key.
case: t => /=; try by move=> *; wp_pures => //.
case; try by move => *; wp_pures.
Qed.

Lemma wp_to_open_key E t Ψ :
  Ψ (repr (Spec.to_open_key t)) ⊢
  WP to_open_key t @ E {{ Ψ }}.
Proof.
rewrite /to_open_key; iIntros "post".
wp_pures; wp_bind (is_key _); iApply wp_is_key.
case: t => /=; try by move=> *; wp_pures => //.
case; try by move => *; wp_pures.
Qed.

End Proofs.
