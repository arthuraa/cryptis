From mathcomp Require Import ssreflect.
From stdpp Require Import gmap coGset.
From iris.algebra Require Import agree auth gset gmap namespace_map.
From iris.base_logic.lib Require Import invariants auth.
From iris.heap_lang Require Import notation proofmode.
From crypto Require Import lib term crypto coGset_disj guarded.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition as_int : val := λ: "t",
  if: Fst "t" = #TInt_tag then SOME (Snd "t")
  else NONE.

Definition tuple : val := λ: "t1" "t2",
  (#TPair_tag, ("t1", "t2")).

Definition untuple : val := λ: "t",
  if: Fst "t" = #TPair_tag then SOME (Snd "t")
  else NONE.

Notation "'bind:' x := e1 'in' e2" :=
  (match: e1 with SOME x => e2  | NONE => NONE end)%E
  (at level 200, x at level 1, e1, e2 at level 200,
  format "'[' 'bind:'  x  :=  '[' e1 ']'  'in'  '/' e2 ']'") : expr_scope.

Definition term_proj : val := rec: "loop" "t" "n" :=
  if: Fst "t" = #TPair_tag then
    if: "n" = #0 then SOME (Fst (Snd "t"))
    else "loop" (Snd (Snd "t")) ("n" - #1)
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

Definition tag (N : namespace) : val := λ: "t",
  tuple (TInt (Zpos (encode N))) "t".

Definition untag (N : namespace) : val := λ: "t",
  bind: "t" := untuple "t" in
  bind: "tag" := as_int (Fst "t") in
  if: "tag" = #(Zpos (encode N))then SOME (Snd "t") else NONE.

Definition mknonce : val := λ: <>,
  let: "n" := ref #() in
  (#TNonce_tag, "n").

Definition is_key : val := λ: "t",
  if: Fst "t" = #TKey_tag then SOME (Fst (Snd "t"))
  else NONE.

Definition enc : val := λ: "k" "t",
  if: (Fst "k" = #TKey_tag) &&
      (Fst (Snd "k") = #(int_of_key_type Enc)) then
    SOME (#TEnc_tag, (Snd (Snd "k"), "t"))
  else NONE.

Definition eq_term : val := (rec: "eq" "x" "y" :=
  if: (Fst "x" = #TInt_tag) && (Fst "y" = #TInt_tag) then
    Snd "x" = Snd "y"
  else if: (Fst "x" = #TPair_tag) && (Fst "y" = #TPair_tag) then
    ("eq" (Fst (Snd "x")) (Fst (Snd "y"))) &&
    ("eq" (Snd (Snd "x")) (Snd (Snd "y")))
  else if: (Fst "x" = #TNonce_tag) && (Fst "y" = #TNonce_tag) then
    Snd "x" = Snd "y"
  else if: (Fst "x" = #TKey_tag) && (Fst "y" = #TKey_tag) then
    (Fst (Snd "x") = Fst (Snd "y")) &&
    "eq" (Snd (Snd "x")) (Snd (Snd "y"))
  else if: (Fst "x" = #TEnc_tag) && (Fst "y" = #TEnc_tag) then
    "eq" (Fst (Snd "x")) (Fst (Snd "y")) &&
    "eq" (Snd (Snd "x")) (Snd (Snd "y"))
  else #false)%V.

Definition dec : val := λ: "k" "t",
  if: (Fst "k" = #TKey_tag)
      && (Fst (Snd "k") = #(int_of_key_type Dec))
      && (Fst "t" = #TEnc_tag)
      && (eq_term (Snd (Snd "k")) (Fst (Snd "t"))) then
    SOME (Snd (Snd "t"))
  else
    NONE.

Definition tenc c : val := λ: "k" "t",
  enc "k" (tag c "t").

Definition tdec c : val := λ: "k" "t",
  bind: "t" := dec "k" "t" in
  untag c "t".

Definition mkkey : val := λ: "k",
  ((#TKey_tag, (#(int_of_key_type Enc), "k")),
   (#TKey_tag, (#(int_of_key_type Dec), "k"))).

Section Proofs.

Context `{!heapG Σ, !cryptoG Σ}.
Notation nonce := loc.

Implicit Types E : coPset.
Implicit Types a : nonce.
Implicit Types l : level.
Implicit Types t : term.
Implicit Types v : val.
Implicit Types Φ : prodO locO termO -n> iPropO Σ.
Implicit Types Ψ : val → iProp Σ.
Implicit Types N : namespace.

Lemma twp_as_int E t Ψ :
  Ψ (repr (Spec.as_int t)) -∗
  WP as_int t @ E [{ Ψ }].
Proof.
rewrite /as_int val_of_termE; iIntros "Hpost"; wp_pures.
case: t; by move=> *; wp_pures; eauto.
Qed.

Lemma wp_as_int E t Ψ :
  Ψ (repr (Spec.as_int t)) -∗
  WP as_int t @ E {{ Ψ }}.
Proof.
by iIntros "?"; iApply twp_wp; iApply twp_as_int.
Qed.

Lemma twp_tuple E t1 t2 Ψ :
  Ψ (TPair t1 t2) -∗
  WP tuple t1 t2 @ E [{ Ψ }].
Proof.
rewrite val_of_termE /tuple; by iIntros "?"; wp_pures.
Qed.

Lemma wp_tuple E t1 t2 Ψ :
  Ψ (TPair t1 t2) -∗
  WP tuple t1 t2 @ E {{ Ψ }}.
Proof.
by iIntros "?"; iApply twp_wp; iApply twp_tuple.
Qed.

Lemma twp_untuple E t Ψ :
  Ψ (repr (Spec.untuple t)) -∗
  WP untuple t @ E [{ Ψ }].
Proof.
iIntros "post".
rewrite /Spec.untuple /untuple /= val_of_termE.
case: t; by move=> *; wp_pures; rewrite -?val_of_termE; iApply "post".
Qed.

Lemma wp_untuple E t Ψ :
  Ψ (repr (Spec.untuple t)) -∗
  WP untuple t @ E {{ Ψ }}.
Proof.
by iIntros "?"; iApply twp_wp; iApply twp_untuple.
Qed.

Lemma twp_term_proj E t (n : nat) Ψ :
  Ψ (repr (Spec.proj t n)) -∗
  WP term_proj t #n @ E [{ Ψ }].
Proof.
rewrite /= val_of_termE; elim: t n Ψ;
try by move=> *; iIntros "?"; wp_rec; wp_pures.
move=> t1 IH1 t2 IH2 [|n] Ψ; iIntros "?"; wp_rec; wp_pures.
  by rewrite -val_of_termE.
rewrite (_ : (S n - 1)%Z = n) /=; try lia.
by iApply IH2.
Qed.

Lemma wp_term_proj E t (n : nat) Ψ :
  Ψ (repr (Spec.proj t n)) -∗
  WP term_proj t #n @ E {{ Ψ }}.
Proof. by iIntros "?"; iApply twp_wp; iApply twp_term_proj. Qed.

Lemma twp_term_of_list E ts Ψ :
  Ψ (repr (Spec.of_list ts)) -∗
  WP term_of_list (repr ts) @ E [{ Ψ }].
Proof.
rewrite /= val_of_termE repr_list_eq Spec.of_list_eq.
elim: ts Ψ => [|t ts IH] Ψ /=; iIntros "post"; wp_rec; wp_pures => //.
wp_bind (term_of_list _); iApply IH; wp_pures.
rewrite -val_of_termE; iApply twp_tuple; wp_pures.
by rewrite val_of_termE.
Qed.

Lemma wp_term_of_list E ts Ψ :
  Ψ (repr (Spec.of_list ts)) -∗
  WP term_of_list (repr ts) @ E {{ Ψ }}.
Proof.
by iIntros "?"; iApply twp_wp; iApply twp_term_of_list.
Qed.

Lemma twp_list_of_term E t Ψ :
  Ψ (repr (Spec.to_list t)) -∗
  WP list_of_term t @ E [{ Ψ }].
Proof.
rewrite val_of_termE /= repr_list_eq.
elim: t Ψ; try by [move=> *; iIntros "post"; wp_rec; wp_pures; iApply "post"].
  move=> n Ψ /=; iIntros "post"; wp_rec; wp_pures.
  case: bool_decide_reflect => [[->]|]; first by wp_pures.
  case: n => *; by wp_pures.
move=> thead _ trest IH Ψ /=; iIntros "post".
wp_rec; wp_pures; wp_bind (list_of_term _); iApply IH.
case: (Spec.to_list trest) => [ts|] /=; wp_pures; eauto.
by rewrite -val_of_termE.
Qed.

Lemma wp_list_of_term E t Ψ :
  Ψ (repr (Spec.to_list t)) -∗
  WP list_of_term t @ E {{ Ψ }}.
Proof.
by iIntros "?"; iApply twp_wp; iApply twp_list_of_term.
Qed.

Lemma twp_list `{!Repr A} (xs : list A) E Ψ :
  Ψ (repr xs) -∗
  WP list_to_expr xs @ E [{ Ψ }].
Proof.
elim: xs Ψ => [|x xs IH] /= Ψ; iIntros "post".
  by iApply (@twp_nil A _).
wp_bind (list_to_expr _); iApply IH.
by iApply (@twp_cons A).
Qed.

Lemma wp_list `{!Repr A} (xs : list A) E Ψ :
  Ψ (repr xs) -∗
  WP list_to_expr xs @ E {{ Ψ }}.
Proof. by iIntros "?"; iApply twp_wp; iApply twp_list. Qed.

Lemma twp_tag E N t Ψ :
  Ψ (repr (Spec.tag N t)) -∗
  WP tag N t @ E [{ Ψ }].
Proof.
iIntros "post".
by rewrite Spec.tag_eq /tag; wp_pures; iApply twp_tuple.
Qed.

Lemma wp_tag E N t Ψ :
  Ψ (repr (Spec.tag N t)) -∗
  WP tag N t @ E {{ Ψ }}.
Proof.
iIntros "post".
by rewrite Spec.tag_eq /tag; wp_pures; iApply wp_tuple.
Qed.

Lemma twp_untag E N t Ψ :
  Ψ (repr (Spec.untag N t)) -∗
  WP untag N t @ E [{ Ψ }].
Proof.
iIntros "post".
rewrite Spec.untag_eq /untag /=; wp_pures.
wp_bind (untuple _); iApply twp_untuple.
case: t; try by [move=> *; wp_pures; iApply "post"].
move=> t1 t2; wp_pures.
wp_bind (as_int _); iApply twp_as_int.
case: t1; try by [move=> *; wp_pures; iApply "post"].
move=> n'; wp_pures.
case: bool_decide_reflect => [[->]|ne]; wp_pures.
  by rewrite decide_left.
case: n' ne; try by move=> *; iApply "post".
move=> n' ne; case: decide => e; try iApply "post".
congruence.
Qed.

Lemma wp_untag E N t Ψ :
  Ψ (repr (Spec.untag N t)) -∗
  WP untag N t @ E {{ Ψ }}.
Proof.
by iIntros "?"; iApply twp_wp; iApply twp_untag.
Qed.

Lemma twp_mknonce E lvl Ψ :
  ↑cryptoN ⊆ E →
  crypto_ctx -∗
  (∀ t, stermT lvl t -∗ ⌜atomic t⌝ -∗
        guarded (lvl = Sec) (unpublished t ⊤) -∗
        crypto_meta_token t ⊤ -∗
        Ψ t) -∗
  WP mknonce #()%V @ E [{ Ψ }].
Proof.
rewrite /mknonce; iIntros (sub) "#ctx post".
wp_pures; wp_bind (ref _)%E; iApply twp_alloc=> //.
iIntros (a) "[_ token]".
iMod (declare_nonce with "ctx token") as "(Ha & own & token)" => //.
iSpecialize ("post" $! (TNonce a)).
rewrite val_of_termE.
by wp_pures; iApply ("post" with "Ha [] own token").
Qed.

Lemma wp_mknonce E lvl Ψ :
  ↑cryptoN ⊆ E →
  crypto_ctx -∗
  (∀ t, stermT lvl t -∗ ⌜atomic t⌝ -∗
        guarded (lvl = Sec) (unpublished t ⊤) -∗
        crypto_meta_token t ⊤ -∗
        Ψ t) -∗
  WP mknonce #()%V @ E {{ Ψ }}.
Proof. by iIntros (?) "#??"; iApply twp_wp; iApply twp_mknonce. Qed.

Lemma twp_mkkey E (k : term) Ψ :
  Ψ (TKey Enc k, TKey Dec k)%V -∗
  WP mkkey k @ E [{ Ψ }].
Proof.
rewrite val_of_termE /= /mkkey.
by iIntros "post"; wp_pures.
Qed.

Lemma wp_mkkey E (k : term) Ψ :
  Ψ (TKey Enc k, TKey Dec k)%V -∗
  WP mkkey k @ E {{ Ψ }}.
Proof.
by iIntros "post"; iApply twp_wp; iApply twp_mkkey.
Qed.

Lemma twp_enc E t1 t2 Ψ :
  Ψ (repr (Spec.enc t1 t2)) -∗
  WP enc t1 t2 @ E [{ Ψ }].
Proof.
rewrite /repr /repr_option /repr /repr_term !val_of_termE /enc.
iIntros "H".
case: t1; try by move=> *; wp_pures; eauto.
case; try by move=> *; wp_pures; eauto.
Qed.

Lemma wp_enc E t1 t2 Ψ :
  Ψ (repr (Spec.enc t1 t2)) -∗
  WP enc t1 t2 @ E {{ Ψ }}.
Proof. by iIntros "?"; iApply twp_wp; iApply twp_enc. Qed.

Lemma twp_eq_term_aux E t1 t2 :
  ⊢ WP (eq_term t1 t2) @ E [{ v, ⌜v = #(bool_decide (t1 = t2))⌝ }].
Proof.
rewrite val_of_termE.
elim: t1 t2=> [n1|t11 IH1 t12 IH2|l1|kt1 t1 IH1|t11 IH1 t12 IH2];
case=> [n2|t21 t22|l2|kt2 t2|t21 t22] /=;
wp_rec; wp_pures=> //.
- iPureIntro; congr (# (LitBool _)).
  apply: bool_decide_iff; intuition congruence.
- wp_bind (eq_term _ _).
  iPoseProof (IH1 t21) as "IH1"; iPoseProof (IH2 t22) as "IH2".
  iApply (twp_wand with "IH1"); iIntros (?) "->".
  case: bool_decide_reflect=> e1.
  + wp_pures; iApply (twp_wand with "IH2"); iIntros (?) "->".
    iPureIntro; congr (# (LitBool _)).
    apply: bool_decide_iff; intuition congruence.
  + wp_pures; iPureIntro; congr (# (LitBool _)).
    rewrite bool_decide_false; congruence.
- iPureIntro; congr (# (LitBool _)).
  apply: bool_decide_iff; intuition congruence.
- case: bool_decide_reflect=> [[/int_of_key_type_inj e1]|e1].
  + wp_pures; iApply twp_wand; first iApply IH1.
    iPureIntro => _ ->; congr (# (LitBool _)).
    apply: bool_decide_iff; intuition congruence.
  + wp_pures; iPureIntro; congr (# (LitBool _)).
    rewrite bool_decide_false; congruence.
- wp_pures; wp_bind (eq_term _ _); iApply twp_wand; first iApply IH1.
  iIntros (?) "->"; case: bool_decide_reflect=> e1; wp_pures; last first.
    iPureIntro; rewrite bool_decide_false //; congruence.
  iApply twp_wand; first iApply IH2.
  iIntros (?) "->"; case: bool_decide_reflect=> e2; wp_pures; last first.
    rewrite bool_decide_false //; congruence.
  iPureIntro; congr (# (LitBool _)).
  by rewrite bool_decide_true //; congruence.
Qed.

Lemma twp_eq_term E t1 t2 Ψ :
  Ψ #(bool_decide (t1 = t2)) -∗
  WP (eq_term t1 t2) @ E [{ Ψ }].
Proof.
iIntros "H".
iApply twp_wand; first iApply twp_eq_term_aux.
by iIntros (?) "->".
Qed.

Lemma wp_eq_term E t1 t2 Ψ :
  Ψ #(bool_decide (t1 = t2)) -∗
  WP (eq_term t1 t2) @ E {{ Ψ }}.
Proof.
by iIntros "H"; iApply twp_wp; iApply twp_eq_term.
Qed.

Lemma twp_dec E t1 t2 Ψ :
  Ψ (repr (Spec.dec t1 t2)) -∗
  WP dec t1 t2 @ E [{ Ψ }].
Proof.
rewrite /repr /repr_option /repr /repr_term !val_of_termE /dec.
iIntros "H".
wp_pures.
case: t1; try by move=> /= *; wp_pures.
case; try by move=> /= *; wp_pures.
move=> tk; wp_pures.
case: t2; try by move=> /= *; wp_pures.
move=> tk' t; wp_pures; rewrite -val_of_termE.
wp_bind (eq_term _ _); iApply twp_eq_term.
by rewrite bool_decide_decide /=; case: decide => [<-|e]; wp_pures.
Qed.

Lemma wp_dec E t1 t2 Ψ :
  Ψ (repr (Spec.dec t1 t2)) -∗
  WP dec t1 t2 @ E {{ Ψ }}.
Proof. by iIntros "?"; iApply twp_wp; iApply twp_dec. Qed.

Lemma twp_tenc E N k t Ψ :
  Ψ (repr (Spec.tenc N k t)) -∗
  WP tenc N k t @ E [{ Ψ }].
Proof.
iIntros "post"; rewrite /tenc; wp_pures.
wp_bind (tag _ _); iApply twp_tag.
by iApply twp_enc.
Qed.

Lemma wp_tenc E N k t Ψ :
  Ψ (repr (Spec.tenc N k t)) -∗
  WP tenc N k t @ E {{ Ψ }}.
Proof. by iIntros "?"; iApply twp_wp; iApply twp_tenc. Qed.

Lemma twp_tdec E N k t Ψ :
  Ψ (repr (Spec.tdec N k t)) -∗
  WP tdec N k t @ E [{ Ψ }].
Proof.
iIntros "post"; rewrite /tdec; wp_pures.
wp_bind (dec _ _); iApply twp_dec.
rewrite /Spec.tdec.
case e: (Spec.dec _ _) => [t'|]; wp_pures => //.
by iApply twp_untag.
Qed.

Lemma wp_tdec E N k t Ψ :
  Ψ (repr (Spec.tdec N k t)) -∗
  WP tdec N k t @ E {{ Ψ }}.
Proof. by iIntros "?"; iApply twp_wp; iApply twp_tdec. Qed.

Lemma twp_is_key E t Ψ :
  Ψ (repr (Spec.is_key t)) -∗
  WP is_key t @ E [{ Ψ }].
Proof.
rewrite /repr /repr_option val_of_termE /is_key.
iIntros "?"; by case: t=> *; wp_pures.
Qed.

Lemma wp_is_key E t Ψ :
  Ψ (repr (Spec.is_key t)) -∗
  WP is_key t @ E {{ Ψ }}.
Proof. by iIntros "?"; iApply twp_wp; iApply twp_is_key. Qed.

End Proofs.
