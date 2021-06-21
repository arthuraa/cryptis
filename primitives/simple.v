From mathcomp Require Import ssreflect.
From mathcomp Require order.
From stdpp Require Import gmap coGset.
From iris.algebra Require Import agree auth gset gmap namespace_map.
From iris.base_logic.lib Require Import invariants auth saved_prop.
From iris.heap_lang Require Import notation proofmode.
From crypto Require Import lib term crypto coGset_disj.
From crypto.primitives Require Import notations comp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition tint : val := λ: "n",
  (#TInt_tag, "n").

Definition as_int : val := λ: "t",
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

Definition tag (N : namespace) : val := λ: "t",
  tuple (TInt (Zpos (encode N))) "t".

Definition untag (N : namespace) : val := λ: "t",
  bind: "t" := untuple "t" in
  bind: "tag" := as_int (Fst "t") in
  if: "tag" = #(Zpos (encode N))then SOME (Snd "t") else NONE.

Definition mknonce : val := λ: <>,
  let: <>  := ref #() in
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

Definition hash : val := λ: "t", (#THash_tag, "t").

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

Definition tgroup : val := λ: "t",
  (#TExp_tag, ("t", NONEV)).

Section Proofs.

Context `{!heapG Σ, !cryptoG Σ}.
Notation nonce := loc.

Implicit Types E : coPset.
Implicit Types a : nonce.
Implicit Types t : term.
Implicit Types v : val.
Implicit Types Φ : prodO locO termO -n> iPropO Σ.
Implicit Types Ψ : val → iProp Σ.
Implicit Types N : namespace.

Class network := Network {
  send : val;
  recv : val;
  wp_send : forall E t Ψ, ▷ pterm t -∗ Ψ #() -∗ WP send t @ E {{ Ψ }};
  wp_recv : forall E Ψ, (∀ t, pterm t -∗ Ψ t) -∗ WP recv #() @ E {{ Ψ }};
}.

Lemma twp_tint E Ψ n : Ψ (TInt n) -∗ WP tint #n @ E [{ Ψ }].
Proof.
by rewrite /tint val_of_term_eq; iIntros "Hpost"; wp_pures.
Qed.

Lemma wp_tint E Ψ n : Ψ (TInt n) -∗ WP tint #n @ E {{ Ψ }}.
Proof. by iIntros "?"; iApply twp_wp; iApply twp_tint. Qed.

Lemma twp_as_int E t Ψ :
  Ψ (repr (Spec.as_int t)) -∗
  WP as_int t @ E [{ Ψ }].
Proof.
rewrite /as_int val_of_term_eq; iIntros "Hpost"; wp_pures.
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
rewrite val_of_term_eq /tuple; by iIntros "?"; wp_pures.
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
rewrite /Spec.untuple /untuple /= val_of_term_eq.
case: t; by move=> *; wp_pures; iApply "post".
Qed.

Lemma wp_untuple E t Ψ :
  Ψ (repr (Spec.untuple t)) -∗
  WP untuple t @ E {{ Ψ }}.
Proof.
by iIntros "?"; iApply twp_wp; iApply twp_untuple.
Qed.

Lemma twp_term_of_list E ts Ψ :
  Ψ (repr (Spec.of_list ts)) -∗
  WP term_of_list (repr ts) @ E [{ Ψ }].
Proof.
rewrite /= [in repr_list ts]repr_list_eq Spec.of_list_eq.
elim: ts Ψ => [|t ts IH] Ψ /=; iIntros "post"; wp_rec; wp_pures.
  by rewrite val_of_term_eq.
wp_bind (term_of_list _); iApply IH; wp_pures.
by iApply twp_tuple; wp_pures.
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
rewrite val_of_term_eq /= repr_list_eq.
elim/term_ind': t Ψ;
try by move=> *; iIntros "post"; wp_rec; wp_pures; iApply "post".
  move=> n Ψ /=; iIntros "post"; wp_rec; wp_pures.
  case: bool_decide_reflect => [[->]|]; first by wp_pures.
  case: n => *; by wp_pures.
move=> thead _ trest IH Ψ /=; iIntros "post".
wp_rec; wp_pures; wp_bind (list_of_term _); iApply IH.
case: (Spec.to_list trest) => [ts|] /=; wp_pures; eauto.
by rewrite -val_of_term_eq.
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

Lemma twp_mknonce E P (Q : term → iProp Σ) Ψ :
  (∀ t, sterm t -∗
        □ (pterm t ↔ ▷ □ P) -∗
        □ (∀ t', dh_pred t t' ↔ ▷ □ Q t') -∗
        nonce_meta_token t ⊤ -∗
        Ψ t) -∗
  WP mknonce #()%V @ E [{ Ψ }].
Proof.
rewrite /mknonce; iIntros "post".
wp_pures; wp_bind (ref _)%E; iApply twp_alloc=> //.
iIntros (a') "[_ token]"; wp_pures.
wp_pures; wp_bind (ref _)%E; iApply twp_alloc=> //.
iIntros (a) "[_ token']".
iMod (saved_prop_alloc P) as (γP) "#own_P".
iMod (saved_pred_alloc Q) as (γQ) "#own_Q".
rewrite (meta_token_difference a (↑nroot.@"nonce")) //.
iDestruct "token'" as "[nonce token']".
iMod (meta_set _ _ γP with "nonce") as "#nonce"; eauto.
rewrite (meta_token_difference a (↑nroot.@"dh")); last solve_ndisj.
iDestruct "token'" as "[dh token']".
iMod (meta_set _ _ γQ with "dh") as "#dh"; eauto.
iMod (meta_set _ _ a' (nroot.@"meta") with "token'") as "#meta"; eauto.
  solve_ndisj.
iSpecialize ("post" $! (TNonce a)).
rewrite val_of_term_eq /=.
wp_pures; iApply ("post" with "[] [] [] [token]"); eauto.
- rewrite sterm_TNonce; iExists _; eauto.
- rewrite pterm_TNonce; iModIntro; iSplit.
  + iDestruct 1 as (γP' P') "(#meta_γP' & #own_P' & ?)".
    iPoseProof (meta_agree with "nonce meta_γP'") as "->".
    iPoseProof (saved_prop_agree with "own_P own_P'") as "e".
    by iModIntro; iRewrite "e".
  + iIntros "#?"; iExists γP, P; eauto.
- iIntros (t'); iModIntro; iSplit.
  + iDestruct 1 as (γQ' Q') "(#meta_γQ' & #own_Q' & ?)".
    iPoseProof (meta_agree with "dh meta_γQ'") as "->".
    iPoseProof (saved_pred_agree _ _ _ t' with "own_Q own_Q'") as "e".
    by iModIntro; iRewrite "e".
  + by iIntros "#?"; iExists _, _; eauto.
Qed.

Lemma wp_mknonce E P Q Ψ :
  (∀ t, sterm t -∗
        □ (pterm t ↔ ▷ □ P) -∗
        □ (∀ t', dh_pred t t' ↔ ▷ □ Q t') -∗
        nonce_meta_token t ⊤ -∗
        Ψ t) -∗
  WP mknonce #()%V @ E {{ Ψ }}.
Proof. by iIntros "?"; iApply twp_wp; iApply twp_mknonce. Qed.

Lemma twp_mkkey E (k : term) Ψ :
  Ψ (TKey Enc k, TKey Dec k)%V -∗
  WP mkkey k @ E [{ Ψ }].
Proof.
rewrite val_of_term_eq /= /mkkey.
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
rewrite /repr /repr_option /repr /repr_term !val_of_term_eq /enc.
iIntros "H".
case: t1; try by move=> *; wp_pures; eauto.
case; try by move=> *; wp_pures; eauto.
Qed.

Lemma wp_enc E t1 t2 Ψ :
  Ψ (repr (Spec.enc t1 t2)) -∗
  WP enc t1 t2 @ E {{ Ψ }}.
Proof. by iIntros "?"; iApply twp_wp; iApply twp_enc. Qed.

Lemma twp_hash E t Ψ : Ψ (THash t) -∗ WP hash t @ E [{ Ψ }].
Proof.
by rewrite /hash val_of_term_eq; iIntros "?"; wp_pures.
Qed.

Lemma wp_hash E t Ψ : Ψ (THash t) -∗ WP hash t @ E {{ Ψ }}.
Proof. by iIntros "?"; iApply twp_wp; iApply twp_hash. Qed.

Lemma twp_dec E t1 t2 Ψ :
  Ψ (repr (Spec.dec t1 t2)) -∗
  WP dec t1 t2 @ E [{ Ψ }].
Proof.
rewrite /repr /repr_option /repr /repr_term !val_of_term_eq /dec.
iIntros "H".
wp_pures.
case: t1; try by move=> /= *; wp_pures.
case; try by move=> /= *; wp_pures.
move=> tk; wp_pures.
case: t2; try by move=> /= *; wp_pures.
move=> tk' t; wp_pures; rewrite -val_of_term_eq.
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
rewrite /repr /repr_option val_of_term_eq /is_key.
iIntros "?"; by case: t=> *; wp_pures.
Qed.

Lemma wp_is_key E t Ψ :
  Ψ (repr (Spec.is_key t)) -∗
  WP is_key t @ E {{ Ψ }}.
Proof. by iIntros "?"; iApply twp_wp; iApply twp_is_key. Qed.

Lemma twp_tgroup E t Ψ :
  Ψ (TExp t []) -∗
  WP tgroup t @ E [{ Ψ }].
Proof.
iIntros "post".
rewrite /tgroup -val_of_pre_term_unfold; wp_pures.
rewrite val_of_pre_term_eq /= unfold_TExp /=.
by rewrite -val_of_pre_term_eq val_of_pre_term_unfold repr_list_eq.
Qed.

Lemma wp_tgroup E t Ψ :
  Ψ (TExp t []) -∗
  WP tgroup t @ E {{ Ψ }}.
Proof. by iIntros "?"; iApply twp_wp; iApply twp_tgroup. Qed.

End Proofs.

Arguments network Σ {_ _}.
