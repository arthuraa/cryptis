From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From crypto Require Import term crypto1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition mknonce : val := λ: <>,
  let: "n" := ref #() in
  (#TNonce_tag, "n").

Definition mkakey : val := λ: <>,
  let: "k" := ref #() in
  ((#TAKey_tag, ("k", #true)), (#TAKey_tag, ("k", #false))).

Definition aenc : val := λ: "k" "t",
  (Fst (Snd "k"), "t").

Definition adec : val := λ: "k" "t",
  if: (Fst "t" = #TAEnc_tag) && (Fst (Snd "k") = Fst (Snd "t")) then
    InjL (Snd (Snd "t"))
  else InjR #().

Definition mkskey : val := λ: <>,
  let: "k" := ref #() in
  (#TSKey_tag, "k").

Definition eq_term : val := (rec: "eq" "x" "y" :=
  if: (Fst "x" = #TInt_tag) && (Fst "y" = #TInt_tag) then
    Snd "x" = Snd "y"
  else if: (Fst "x" = #TPair_tag) && (Fst "y" = #TPair_tag) then
    ("eq" (Fst (Snd "x")) (Fst (Snd "y"))) &&
    ("eq" (Snd (Snd "x")) (Snd (Snd "y")))
  else if: (Fst "x" = #TNonce_tag) && (Fst "y" = #TNonce_tag) then
    Snd "x" = Snd "y"
  else if: (Fst "x" = #TAKey_tag) && (Fst "y" = #TAKey_tag) then
    (Fst (Snd "x") = Fst (Snd "y")) &&
    (Snd (Snd "x") = Snd (Snd "y"))
  else if: (Fst "x" = #TAEnc_tag) && (Fst "y" = #TAEnc_tag) then
    (Fst (Snd "x") = Fst (Snd "y")) &&
    ("eq" (Snd (Snd "x")) (Snd (Snd "y")))
  else if: (Fst "x" = #TSKey_tag) && (Fst "y" = #TSKey_tag) then
    Snd "x" = Snd "y"
  else if: (Fst "x" = #TSEnc_tag) && (Fst "y" = #TSEnc_tag) then
    (Fst (Snd "x") = Fst (Snd "y")) &&
    ("eq" (Snd (Snd "x")) (Snd (Snd "y")))
  else #false)%V.

Definition resN := nroot .@ "res".

Section Proofs.

Context `{!heapG Σ, !resG Σ}.

Implicit Types E : coPset.
Implicit Types l : loc.
Implicit Types rs : readers.
Implicit Types v : val.

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
               ∗ nonceT rs l}].
Proof.
move=> HE; iIntros "#? #wf_rs"; rewrite /mknonce.
wp_pures; wp_alloc l as "Hl"; iApply fupd_twp.
iInv resN as "Hinv" "Hclose".
iMod (res_alloc _ (RNonce rs) l with "Hinv Hl wf_rs") as "[Hinv Hown]".
iMod ("Hclose" with "Hinv") as "_".
by iModIntro; wp_pures; eauto.
Qed.

Lemma twp_mkakey E rs_enc rs_dec Φ :
  ↑resN ⊆ E →
  res_ctx -∗
  wf_readers rs_enc -∗
  wf_readers rs_dec -∗
  WP mkakey #()%V @ E
     [{v, ∃ l, ⌜v = (val_of_term (TAKey l true),
                     val_of_term (TAKey l false))%V⌝
               ∗ akeyT rs_enc rs_dec Φ l}].
Proof.
move=> HE; iIntros "#? #wf_enc #wf_dec"; rewrite /mkakey.
wp_pures; wp_alloc l as "Hl"; iApply fupd_twp.
iInv resN as "Hinv" "Hclose".
iMod (res_alloc _ (RAKey rs_enc rs_dec Φ) l
        with "Hinv Hl [wf_enc wf_dec]") as "[Hinv Hown]".
  by rewrite /=; eauto.
iMod ("Hclose" with "Hinv") as "_".
by iModIntro; wp_pures; eauto.
Qed.

Lemma twp_mkskey E rs Φ :
  ↑resN ⊆ E →
  res_ctx -∗
  wf_readers rs -∗
  WP mkskey #()%V @ E
     [{v, ∃ l, ⌜v = val_of_term (TSKey l)⌝
               ∗ skeyT rs Φ l}].
Proof.
move=> HE; iIntros "#? #wf_rs"; rewrite /mkskey.
wp_pures; wp_alloc l as "Hl"; iApply fupd_twp.
iInv resN as "Hinv" "Hclose".
iMod (res_alloc _ (RSKey rs Φ) l
        with "Hinv Hl wf_rs") as "[Hinv Hown]".
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
