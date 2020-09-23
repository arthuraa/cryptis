From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From crypto Require Import lib term crypto1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

Definition mknonce : val := λ: <>,
  let: "n" := ref #() in
  (#TNonce_tag, "n").

Definition is_key : val := λ: "t",
  if: Fst "t" = #TKey_tag then SOME (Fst (Snd "t"))
  else NONE.

Definition enc : val := λ: "k" "t",
  if: (Fst "k" = #TKey_tag) &&
      (Fst (Snd "k") = #(int_of_key_type KAEnc)) then
    SOME (#TEnc_tag, (#true, Snd (Snd "k"), "t"))
  else if: (Fst "k" = #TKey_tag) &&
           (Fst (Snd "k") = #(int_of_key_type KSym)) then
    SOME (#TEnc_tag, (#false, Snd (Snd "k"), "t"))
  else NONE.

Definition dec : val := λ: "k" "t",
  if: (Fst "k" = #TKey_tag)
      && (Fst (Snd "k") = #(int_of_key_type KADec))
      && (Fst "t" = #TEnc_tag)
      && Fst (Fst (Snd "t"))
      && (Snd (Snd "k") = Snd (Fst (Snd "t"))) then
    SOME (Snd (Snd "t"))
  else if: (Fst "k" = #TKey_tag)
      && (Fst (Snd "k") = #(int_of_key_type KSym))
      && (Fst "t" = #TEnc_tag)
      && (~ Fst (Fst (Snd "t")))
      && (Snd (Snd "k") = Snd (Fst (Snd "t"))) then
    SOME (Snd (Snd "t"))
  else
    NONE.

Definition mkakey : val := λ: <>,
  let: "k" := ref #() in
  ((#TKey_tag, (#(int_of_key_type KAEnc), "k")),
   (#TKey_tag, (#(int_of_key_type KADec), "k"))).

Definition mkskey : val := λ: <>,
  let: "k" := ref #() in
  (#TKey_tag, (#(int_of_key_type KSym), "k")).

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
    (Snd (Snd "x") = Snd (Snd "y"))
  else if: (Fst "x" = #TEnc_tag) && (Fst "y" = #TEnc_tag) then
    (Fst (Fst (Snd "x")) = Fst (Fst (Snd "y"))) &&
    (Snd (Fst (Snd "x")) = Snd (Fst (Snd "y"))) &&
    ("eq" (Snd (Snd "x")) (Snd (Snd "y")))
  else #false)%V.

Section Proofs.

Context `{!heapG Σ, !resG Σ}.

Implicit Types E : coPset.
Implicit Types l : loc.
Implicit Types lvl : level.
Implicit Types t : term.
Implicit Types v : val.

Lemma twp_tuple E t1 t2 :
  ⊢ WP tuple t1 t2 @ E
       [{v, ⌜v = TPair t1 t2⌝}].
Proof. by rewrite val_of_termE /tuple; wp_pures. Qed.

Lemma twp_untuple E t :
  ⊢ WP untuple t @ E
       [{v, ⌜v = match t with
                 | TPair t1 t2 => SOMEV (t1, t2)
                 | _ => NONEV
                 end⌝}].
Proof.
rewrite val_of_termE /untuple.
by case: t=> *; wp_pures.
Qed.

Lemma twp_term_proj E t (n : nat) :
  ⊢ WP term_proj t #n @ E
       [{v, ⌜v = repr (Spec.proj t n)⌝}].
Proof.
rewrite val_of_termE; elim: t n; try by move=> *; wp_rec; wp_pures.
move=> t1 IH1 t2 IH2 [|n]; wp_rec; wp_pures.
  by rewrite -val_of_termE.
rewrite (_ : (S n - 1)%Z = n) /=; try lia.
by iApply IH2.
Qed.

Lemma twp_mknonce E lvl :
  ⊢ WP mknonce #()%V @ E
       [{v, ∃ l, ⌜v = TNonce l⌝ ∗ nonceT lvl l
                 ∗ meta_token l (⊤ ∖ ↑cryptoN.@"res")}].
Proof.
rewrite /mknonce.
wp_pures; wp_bind (ref _)%E; iApply twp_alloc=> //.
iIntros (l) "[Hl Hmeta]".
rewrite (meta_token_difference l (↑cryptoN.@"res")) //.
iDestruct "Hmeta" as "[Hmeta1 Hmeta2]".
iMod (res_alloc (RNonce lvl) l with "Hmeta1") as "Hinv"=> //.
by wp_pures; rewrite val_of_termE; eauto.
Qed.

Lemma twp_mkakey E lvl_enc lvl_dec Φ :
  ⊢ WP mkakey #()%V @ E
       [{v, ∃ l, ⌜v = (TKey KAEnc l, TKey KADec l)%V⌝
                 ∗ akeyT lvl_enc lvl_dec Φ l
                 ∗ meta_token l (⊤ ∖ ↑cryptoN.@"res")}].
Proof.
rewrite /mkakey.
wp_pures; wp_bind (ref _)%E; iApply twp_alloc=> //.
iIntros (l) "[Hl Hmeta]".
rewrite (meta_token_difference l (↑cryptoN.@"res")) //.
iDestruct "Hmeta" as "[Hmeta1 Hmeta2]".
iMod (res_alloc (RAKey lvl_enc lvl_dec Φ) l with "Hmeta1") as "#Hown"=> //.
by wp_pures; rewrite val_of_termE /=; iExists l; iSplit; eauto.
Qed.

Lemma twp_enc E t1 t2  :
  ⊢ WP enc t1 t2 @ E [{v, ⌜v = repr (Spec.enc t1 t2)⌝}].
Proof.
rewrite /repr /repr_option /repr /repr_term !val_of_termE /enc.
case: t1; try by move=> *; wp_pures; eauto.
case; try by move=> *; wp_pures; eauto.
Qed.

Lemma twp_dec E t1 t2 :
  ⊢ WP dec t1 t2 @ E [{v, ⌜v = repr (Spec.dec t1 t2)⌝}].
Proof.
rewrite /repr /repr_option /repr /repr_term !val_of_termE /dec.
wp_pures.
case: t1; try by move=> /= *; wp_pures.
case; try by move=> /= *; wp_pures.
- move=> l1; wp_pures.
  case: t2; try by move=> /= *; wp_pures.
  case; try by move=> /= *; wp_pures.
  move=> /= l2 t; wp_pures.
  case: decide=> [<-|ne]; last first.
    rewrite bool_decide_false; try congruence.
    by wp_pures.
  by rewrite bool_decide_true //; wp_pures.
- move=> l1; wp_pures.
  case: t2; try by move=> /= *; wp_pures.
  case; try by move=> /= *; wp_pures.
  move=> /= l2 t; wp_pures.
  case: decide=> [<-|ne]; last first.
    rewrite bool_decide_false; try congruence.
    by wp_pures.
  by rewrite bool_decide_true //; wp_pures.
Qed.

Lemma twp_is_key E t : 
  ⊢ WP is_key t @ E
       [{v, ⌜v = repr (Spec.is_key t)⌝}].
Proof.
rewrite /repr /repr_option val_of_termE /is_key.
by case: t=> *; wp_pures.
Qed.

Lemma twp_mkskey E rs Φ :
  ⊢ WP mkskey #()%V @ E
       [{v, ∃ l, ⌜v = TKey KSym l⌝ ∗ skeyT rs Φ l
                 ∗ meta_token l (⊤ ∖ ↑cryptoN.@"res")}].
Proof.
rewrite /mkskey.
wp_pures; wp_bind (ref _)%E; iApply twp_alloc=> //.
iIntros (l) "[Hl Hmeta]".
rewrite (meta_token_difference l (↑cryptoN.@"res")) //.
iDestruct "Hmeta" as "[Hmeta1 Hmeta2]".
iMod (res_alloc (RSKey rs Φ) l with "Hmeta1") as "#Hres"=> //.
by wp_pures; rewrite val_of_termE; iExists l; repeat iSplit=> //.
Qed.

Lemma twp_eq_term E t1 t2 :
  ⊢ WP (eq_term t1 t2) @ E [{ v, ⌜v = #(bool_decide (t1 = t2))⌝ }].
Proof.
rewrite val_of_termE.
elim: t1 t2=> [n1|t11 IH1 t12 IH2|l1|kt1 l1|b1 l1 t1 IH1];
case=> [n2|t21 t22|l2|kt2 l2|b2 l2 t2] /=;
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
  + wp_pures; iPureIntro; congr (# (LitBool _)).
    apply: bool_decide_iff; intuition congruence.
  + wp_pures; iPureIntro; congr (# (LitBool _)).
    rewrite bool_decide_false; congruence.
- case: bool_decide_reflect=> e1; wp_pures; last first.
    rewrite bool_decide_false //; congruence.
  case: bool_decide_reflect=> e2; wp_pures; last first.
    rewrite bool_decide_false //; congruence.
  iPoseProof (IH1 t2) as "IH1".
  iApply (twp_wand with "IH1"); iIntros (?) "->".
  iPureIntro; congr (# (LitBool _)).
  apply: bool_decide_iff; intuition congruence.
Qed.

End Proofs.
