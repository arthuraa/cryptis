(* These proofs take much longer to check than the rest of the
development. Since they don't have many dependencies, they are left in their own
file to avoid slowing down the compilation process. *)

From cryptis Require Import lib.
From mathcomp Require Import ssreflect.
From mathcomp Require order.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import term.
From cryptis.primitives Require Import notations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition eq_term : val := (rec: "eq" "x" "y" :=
  if: (Fst "x" = Fst "y") then
    let: "tag" := Fst "x" in
    if: "tag" = #TInt_tag then
      Snd "x" = Snd "y"
    else if: "tag" = #TPair_tag then
      ("eq" (Fst (Snd "x")) (Fst (Snd "y"))) &&
      ("eq" (Snd (Snd "x")) (Snd (Snd "y")))
    else if: "tag" = #TNonce_tag then
      Snd "x" = Snd "y"
    else if: "tag" = #TKey_tag then
      (Fst (Snd "x") = Fst (Snd "y")) &&
      "eq" (Snd (Snd "x")) (Snd (Snd "y"))
    else if: "tag" = #TSeal_tag then
      "eq" (Fst (Snd "x")) (Fst (Snd "y")) &&
      "eq" (Snd (Snd "x")) (Snd (Snd "y"))
    else if: "tag" = #THash_tag then
      "eq" (Snd "x") (Snd "y")
    else if: "tag" = #TExp_tag then
      "eq" (Fst (Snd "x")) (Fst (Snd "y")) &&
      eq_list "eq" (Snd (Snd "x")) (Snd (Snd "y"))
    else #false
  else #false)%V.

Definition leq_term : val := rec: "loop" "t1" "t2" :=
 (if: (Fst "t1" < Fst "t2") then #true
  else if: (Fst "t1" = Fst "t2") then
    let: "tag" := Fst "t1" in
    let: "a1"  := Snd "t1" in
    let: "a2"  := Snd "t2" in
    if: "tag" = #TInt_tag then "a1" ≤ "a2"
    else if: "tag" = #TPair_tag then
      let: "t11" := Fst "a1" in
      let: "t12" := Snd "a1" in
      let: "t21" := Fst "a2" in
      let: "t22" := Snd "a2" in
      if: eq_term "t11" "t21" then "loop" "t12" "t22"
      else "loop" "t11" "t21"
    else if: "tag" = #TNonce_tag then
      leq_loc "a1" "a2"
    else if: "tag" = #TKey_tag then
      let: "kt1" := Fst "a1" in
      let: "t1"  := Snd "a1" in
      let: "kt2" := Fst "a2" in
      let: "t2"  := Snd "a2" in
      if: "kt1" = "kt2" then "loop" "t1" "t2"
      else "kt1" ≤ "kt2"
    else if: "tag" = #TSeal_tag then
      let: "t11" := Fst "a1" in
      let: "t12" := Snd "a1" in
      let: "t21" := Fst "a2" in
      let: "t22" := Snd "a2" in
      if: eq_term "t11" "t21" then "loop" "t12" "t22"
      else "loop" "t11" "t21"
    else if: "tag" = #THash_tag then
      "loop" "a1" "a2"
    else if: "tag" = #TExp_tag then
      let: "t1" := Fst "a1" in
      let: "ts1" := Snd "a1" in
      let: "t2" := Fst "a2" in
      let: "ts2" := Snd "a2" in
      if: eq_term "t1" "t2" then
        leq_list eq_term "loop" "ts1" "ts2"
      else "loop" "t1" "t2"
    else #false
  else #false)%V.

Definition texp : val := λ: "t1" "t2",
  if: Fst "t1" = #TExp_tag then
    let: "base" := Fst (Snd "t1") in
    let: "exp"  := Snd (Snd "t1") in
    (#TExp_tag, ("base", insert_sorted leq_term "t2" "exp"))
  else (#TExp_tag, ("t1", ["t2"])).

Section Proofs.

Context `{!heapGS Σ}.
Notation nonce := loc.

Implicit Types E : coPset.
Implicit Types a : nonce.
Implicit Types t : term.
Implicit Types v : val.
Implicit Types Ψ : val → iProp Σ.
Implicit Types N : namespace.

Lemma twp_eq_pre_term_aux E (pt1 pt2 : PreTerm.pre_term) :
  ⊢ WP (eq_term (repr pt1) (repr pt2)) @ E
       [{ v, ⌜v = #(bool_decide (pt1 = pt2))⌝ }].
Proof.
rewrite /= val_of_pre_term_unseal.
elim: pt1 pt2
  => [n1|t11 IH1 t12 IH2|l1|kt1 t1 IH1|t11 IH1 t12 IH2|t1 IH|t1 IHt1 ts1 IHts1];
case=> [n2|t21 t22|l2|kt2 t2|t21 t22|t2|t2 ts2] /=;
wp_rec; wp_pures=> //.
- iPureIntro; congr (# (LitBool _)).
  apply: bool_decide_ext; intuition congruence.
- wp_bind (eq_term _ _).
  iPoseProof (IH1 t21) as "IH1"; iPoseProof (IH2 t22) as "IH2".
  iApply (twp_wand with "IH1"); iIntros (?) "->".
  case: bool_decide_reflect=> e1.
  + wp_pures; iApply (twp_wand with "IH2"); iIntros (?) "->".
    iPureIntro; congr (# (LitBool _)).
    apply: bool_decide_ext; intuition congruence.
  + wp_pures; iPureIntro; congr (# (LitBool _)).
    rewrite bool_decide_false; congruence.
- iPureIntro; congr (# (LitBool _)).
  apply: bool_decide_ext; intuition congruence.
- case: bool_decide_reflect=> [[/int_of_key_type_inj e1]|e1].
  + wp_pures; iApply twp_wand; first iApply IH1.
    iPureIntro => _ ->; congr (# (LitBool _)).
    apply: bool_decide_ext; intuition congruence.
  + wp_pures; iPureIntro; congr (# (LitBool _)).
    rewrite bool_decide_false; congruence.
- wp_pures; wp_bind (eq_term _ _); iApply twp_wand; first iApply IH1.
  iIntros (?) "->"; case: bool_decide_reflect=> e1; wp_pures; last first.
    iPureIntro; rewrite bool_decide_false //; congruence.
  iApply twp_wand; first iApply IH2.
  iIntros (?) "->"; case: bool_decide_reflect=> e2; last first.
    rewrite bool_decide_false //; congruence.
  iPureIntro; congr (# (LitBool _)).
  by rewrite bool_decide_true //; congruence.
- wp_pures; iApply twp_wand; first iApply IH.
  iIntros (?) "->"; iPureIntro; congr (# (LitBool _)).
  apply: bool_decide_ext; intuition congruence.
- wp_bind (eq_term _ _); iApply twp_wand; first iApply IHt1.
  iIntros (?) "->"; case: bool_decide_reflect=> e1; wp_pures; last first.
    rewrite bool_decide_false //; congruence.
  rewrite -val_of_pre_term_unseal -!repr_list_val.
  iApply (@twp_eq_list PreTerm.pre_term); last first.
    iPureIntro; congr (# (LitBool _)); apply: bool_decide_ext.
    rewrite e1; split; congruence.
  rewrite /=.
  elim: ts1 IHts1 {e1} => //= [|x1 ts1 IH].
    by move=> *; exfalso; set_solver.
  case=> IHx1 /IH IHts1 x1' x2' Ψ.
  rewrite elem_of_cons; case=> [->|x1'_in]; iIntros "post"; last first.
    by iApply IHts1.
  rewrite -/val_of_pre_term val_of_pre_term_unseal.
  iApply twp_wand; first iApply IHx1; by iIntros (?) "->".
Qed.

Lemma twp_eq_pre_term E (pt1 pt2 : PreTerm.pre_term) Ψ :
  Ψ #(bool_decide (pt1 = pt2)) ⊢
  WP (eq_term (repr pt1) (repr pt2)) @ E [{ Ψ }].
Proof.
iIntros "H".
iApply twp_wand; first iApply twp_eq_pre_term_aux.
by iIntros (?) "->".
Qed.

Lemma twp_eq_term E t1 t2 Ψ :
  Ψ #(bool_decide (t1 = t2)) ⊢
  WP (eq_term t1 t2) @ E [{ Ψ }].
Proof.
iIntros "H".
rewrite -!val_of_pre_term_unfold.
iApply twp_wand; first iApply twp_eq_pre_term_aux.
iIntros (?) "->".
rewrite (_ : bool_decide (t1 = t2) =
             bool_decide (unfold_term t1 = unfold_term t2)) //.
by apply: bool_decide_ext; split => [->|/unfold_term_inj] //.
Qed.

Lemma wp_eq_term E t1 t2 Ψ :
  Ψ #(bool_decide (t1 = t2)) ⊢
  WP (eq_term t1 t2) @ E {{ Ψ }}.
Proof.
by iIntros "H"; iApply twp_wp; iApply twp_eq_term.
Qed.

Import ssrbool seq path.

Import ssreflect.eqtype ssreflect.order.

Lemma twp_leq_pre_term E (pt1 pt2 : PreTerm.pre_term) Ψ :
  Ψ #(pt1 <= pt2)%O ⊢
  WP (leq_term (repr pt1) (repr pt2)) @ E [{ Ψ }].
Proof.
rewrite /= val_of_pre_term_unseal.
elim: pt1 pt2 Ψ
  => [n1|t11 IH1 t12 IH2|l1|kt1 t1 IH1|t11 IH1 t12 IH2|t1 IH|t1 IHt1 ts1 IHts1];
case=> [n2|t21 t22|l2|kt2 t2|t21 t22|t2|t2 ts2] /= Ψ;
iIntros "post"; wp_rec; wp_pures; try by iApply "post".
- rewrite PreTerm.leqE /= (_ : (_ <= _)%O = bool_decide (n1 ≤ n2)%Z) //.
  exact/(sameP (Z.leb_spec0 _ _))/bool_decide_reflect.
- rewrite -{1 2}val_of_pre_term_unseal; wp_bind (eq_term _ _).
  rewrite PreTerm.leqE /=; iApply twp_eq_pre_term.
  rewrite eq_op_bool_decide; case: eqP => [->|_]; wp_pures.
    by iApply IH2.
  by iApply IH1.
- by rewrite PreTerm.leqE /=; iApply twp_leq_loc.
- rewrite PreTerm.leqE /=; case: eqP => [->|neq].
    rewrite bool_decide_eq_true_2 //; wp_pures; by iApply IH1.
  rewrite bool_decide_eq_false_2; last first.
    move=> [e]; apply: neq.
    by apply: int_of_key_type_inj.
  wp_pures.
  by case: kt1 kt2 {neq} => [] [].
- rewrite PreTerm.leqE /=; wp_bind (eq_term _ _).
  rewrite -{1 2}val_of_pre_term_unseal; iApply twp_eq_pre_term.
  rewrite eq_op_bool_decide; case: eqP => [->|neq]; wp_pures.
    by iApply IH2.
  by iApply IH1.
- rewrite PreTerm.leqE /=; by iApply IH.
- rewrite PreTerm.leqE /=; wp_bind (eq_term _ _).
  rewrite -{1 2}val_of_pre_term_unseal.
  iApply twp_eq_pre_term; rewrite eq_op_bool_decide.
  case: eqP=> [->|neq]; wp_pures; last by iApply IHt1.
  rewrite -!repr_list_val -val_of_pre_term_unseal; iApply twp_leq_list => //.
  + move=> pt1 pt2 Ψ'; iIntros "_ post".
    by iApply twp_eq_pre_term; rewrite eq_op_bool_decide; iApply "post".
  + move/foldr_in in IHts1.
    move=> ????; iIntros "_ post".
    by rewrite /= val_of_pre_term_unseal; iApply IHts1 => //; iApply "post".
  + by iIntros "_".
Qed.

Lemma twp_leq_term E t1 t2 Ψ :
  Ψ #(t1 <= t2)%O ⊢
  WP leq_term t1 t2 @ E [{ Ψ }].
Proof.
rewrite -2!val_of_pre_term_unfold.
by iApply twp_leq_pre_term.
Qed.

Lemma twp_texp E t1 t2 Ψ :
  Ψ (TExp t1 t2) ⊢
  WP texp t1 t2 @ E [{ Ψ }].
Proof.
iIntros "post"; rewrite /texp /=; wp_pures; wp_bind (Fst _ = _)%E.
iApply (twp_wand _ _ _ (λ v, ⌜v = #(is_exp t1)⌝)%I).
  rewrite -val_of_pre_term_unfold.
  rewrite is_exp_unfold val_of_pre_term_unseal.
  by case: (unfold_term t1) =>> //=; wp_pures.
iIntros "% ->"; case: (boolP (is_exp t1)) => [t1X|t1NX].
- rewrite -!val_of_pre_term_unfold unfold_TExpN /=.
  rewrite /PreTerm.exp /=.
  wp_pures. rewrite is_exp_unfold in t1X.
  rewrite val_of_pre_term_unseal /=.
  case: (unfold_term t1) (wf_unfold_term t1) t1X => //= pt pts.
  case/and5P=> ???? sorted_pts _. wp_pures.
  wp_bind (insert_sorted _ _ _).
  rewrite -val_of_pre_term_unseal -!repr_list_val.
  iApply (@twp_insert_sorted _
            (Order.Total.Pack (Order.Total.on PreTerm.pre_term))) => //.
    move=> * /=; iIntros "_ post".
    by iApply twp_leq_pre_term; iApply "post".
  iIntros "_"; wp_pures.
  have -> : sort Order.le (pts ++ [:: unfold_term t2])
            = sort Order.le (unfold_term t2 :: pts).
    by apply/perm_sort_leP; rewrite perm_catC.
  by [].
- wp_pures.
  rewrite -!val_of_pre_term_unfold unfold_TExpN /PreTerm.exp /=.
  rewrite is_exp_unfold in t1NX.
  rewrite PreTerm.base_expN // PreTerm.exps_expN //= sortE /=.
  rewrite val_of_pre_term_unseal /=.
  rewrite /CONS. wp_pures.
  by rewrite repr_list_unseal /=.
Qed.

Lemma wp_texp E t1 t2 Ψ :
  Ψ (TExp t1 t2) ⊢
  WP texp t1 t2 @ E {{ Ψ }}.
Proof. by iIntros "post"; iApply twp_wp; iApply twp_texp. Qed.

End Proofs.
