From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From crypto Require Import term crypto1.

Definition mknonce : val := λ: <>,
  let: "n" := ref #() in
  (#2, "n").

Definition eq_term : val := (rec: "eq" "x" "y" :=
  if: (Fst "x" = #0) && (Fst "y" = #0) then
    Snd "x" = Snd "y"
  else if: (Fst "x" = #1) && (Fst "y" = #1) then
    ("eq" (Fst (Snd "x")) (Fst (Snd "y"))) &&
    ("eq" (Snd (Snd "x")) (Snd (Snd "y")))
  else if: (Fst "x" = #2) && (Fst "y" = #2) then
    Snd "x" = Snd "y"
  else if: (Fst "x" = #3) && (Fst "y" = #3) then
    (Fst (Snd "x") = Fst (Snd "y")) &&
    (Snd (Snd "x") = Snd (Snd "y"))
  else if: (Fst "x" = #4) && (Fst "y" = #4) then
    (Fst (Snd "x") = Fst (Snd "y")) &&
    ("eq" (Snd (Snd "x")) (Snd (Snd "y")))
  else if: (Fst "x" = #5) && (Fst "y" = #5) then
    Snd "x" = Snd "y"
  else if: (Fst "x" = #6) && (Fst "y" = #6) then
    (Fst (Snd "x") = Fst (Snd "y")) &&
    ("eq" (Snd (Snd "x")) (Snd (Snd "y")))
  else #false)%V.

Definition resN := nroot .@ "res".

Section Proofs.

Context `{!heapG Σ, !resG Σ}.

Implicit Types E : coPset.
Implicit Types rs : readers.

Definition res_ctx : iProp Σ :=
  inv resN res_inv.

Global Instance persistent_res_ctx : Persistent res_ctx.
Proof. apply _. Qed.

Lemma twp_mknonce E rs :
  ↑resN ⊆ E →
  res_ctx -∗
  wf_readers rs -∗
  WP mknonce #()%V @ E
     [{v, ∃ l, ⌜v = val_of_term (TNonce l)⌝
               ∗ nonceT l rs}].
Proof.
move=> HE; iIntros "#? #wf_rs"; rewrite /mknonce.
wp_pures; wp_alloc l as "Hl"; iApply fupd_twp.
iInv resN as (RM1) "[Hown >wf_RM1]" "Hclose".
iMod (later_own with "Hown") as (a) "[Hown Ha]".
case: a=> [aa af]; rewrite auth_equivI /=.
iDestruct "Ha" as "[Ha >Haf]"; iRewrite -"Haf" in "Hown".
rewrite option_equivI; case: aa=> [[q a]|]; last by iMod "Ha" as "[]".
rewrite prod_equivI /=; iDestruct "Ha" as "[> <- #Ha]".
iPoseProof (own_valid with "Hown") as "#Hvalid".
rewrite auth_validI /=.
iDestruct "Hvalid" as "(_&Hvalid)".
iDestruct "Hvalid" as (RR) "(e & _ & Hvalid)".
iRewrite "e" in "Hown"; iRewrite "e" in "Ha"; iClear "e"; clear a af.
rewrite -[Auth _ _]/(● RR) agree_equivI.
iDestruct (to_resR_uninjI with "Hvalid") as (RM2) "e".
iRewrite -"e" in "Hown"; iRewrite -"e" in "Ha".
rewrite to_resR_equivI.
iAssert (▷ (dom (gset loc) RM1 ≡ dom (gset loc) RM2))%I as "> %e".
  by iModIntro; iRewrite "Ha".
iAssert (⌜l ∉ dom (gset loc) RM2⌝)%I as "%Hfresh".
  rewrite -e elem_of_dom; iIntros "%contra".
  case: contra=> v RM_l; rewrite big_sepM_delete //.
  iDestruct "wf_RM1" as "[[Hl' _] _]".
  by iPoseProof (mapsto_valid_2 with "Hl Hl'") as "%".
iMod (own_update _ _ (_ ⋅ ◯ {[l := to_agree (RNonce rs)]}) with "Hown")
    as "[Hown ?]".
  apply auth_update_alloc, alloc_singleton_local_update; last done.
  by rewrite -not_elem_of_dom dom_fmap.
iAssert (▷ res_inv)%I with "[Hl wf_RM1 Hown]" as "Hinv".
  iModIntro. iRewrite -"Ha" in "Hown".
  iExists (<[l:=RNonce rs]> RM1).
  rewrite -fmap_insert; iFrame.
  rewrite big_sepM_insert /=; first by iFrame.
  by apply/not_elem_of_dom; rewrite e.
iMod ("Hclose" with "Hinv") as "_".
by iModIntro; wp_pures; eauto.
Qed.

Lemma twp_eq_term t1 t2 :
  ⊢ WP (eq_term (val_of_term t1) (val_of_term t2))
       [{ v, ⌜v = #(bool_decide (t1 = t2))⌝ }].
Proof.
elim: t1 t2=> [n1|t11 IH1 t12 IH2|l1|l1 b1|l1 t1 IH1|l1|l1 t1 IH1];
case=> [n2|t21 t22|l2|l2 b2|l2 t2|l2|l2 t2] /=;
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
- case: bool_decide_reflect=> e1.
  + wp_pures; iPureIntro; congr (# (LitBool _)).
    apply: bool_decide_iff; intuition congruence.
  + wp_pures; iPureIntro; congr (# (LitBool _)).
    rewrite bool_decide_false; congruence.
- case: bool_decide_reflect=> e1.
  + wp_pures.
    iPoseProof (IH1 t2) as "IH1".
    iApply (twp_wand with "IH1"); iIntros (?) "->".
    iPureIntro; congr (# (LitBool _)).
    apply: bool_decide_iff; intuition congruence.
  + wp_pures; iPureIntro; congr (# (LitBool _)).
    rewrite bool_decide_false; congruence.
- iPureIntro; congr (# (LitBool _)).
  apply: bool_decide_iff; intuition congruence.
- case: bool_decide_reflect=> e1.
  + wp_pures.
    iPoseProof (IH1 t2) as "IH1".
    iApply (twp_wand with "IH1"); iIntros (?) "->".
    iPureIntro; congr (# (LitBool _)).
    apply: bool_decide_iff; intuition congruence.
  + wp_pures; iPureIntro; congr (# (LitBool _)).
    rewrite bool_decide_false; congruence.
Qed.

End Proofs.
