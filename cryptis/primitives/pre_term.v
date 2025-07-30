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
From cryptis.core Require Import pre_term.
From cryptis.primitives Require Import notations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition eq_term_op0 : val := λ: "x" "y",
  (Fst "x" = Fst "y") && (Snd "x" = Snd "y").

Definition eq_key_type : val := λ: "x" "y",
  "x" = "y".

Definition eq_term_op1 : val := λ: "x" "y",
  if: (Fst "x" = Fst "y") then
    let: "tag" := Fst "x" in
    if: "tag" = #0 (* Key *) then
      eq_key_type (Snd "x") (Snd "y")
    else (* Hash *) #true
  else #false.

Definition eq_term_op2 : val := λ: "x" "y",
  "x" = "y".

Definition eq_term : val := (rec: "eq" "x" "y" :=
  if: (Fst "x" = Fst "y") then
    let: "tag" := Fst "x" in
    if: "tag" = #TOp0_tag then
      eq_term_op0 (Snd "x") (Snd "y")
    else if: "tag" = #TOp1_tag then
      eq_term_op1 (Fst (Snd "x")) (Fst (Snd "y")) &&
      "eq" (Snd (Snd "x")) (Snd (Snd "y"))
    else if: "tag" = #TOp2_tag then
      eq_term_op2 (Fst (Fst (Snd "x"))) (Fst (Fst (Snd "y"))) &&
      "eq" (Snd (Fst (Snd "x"))) (Snd (Fst (Snd "y"))) &&
      "eq" (Snd (Snd "x")) (Snd (Snd "y"))
    else if: "tag" = #TExp_tag then
      "eq" (Fst (Snd "x")) (Fst (Snd "y")) &&
      eq_list "eq" (Snd (Snd "x")) (Snd (Snd "y"))
    else #false
  else #false)%V.

Definition leq_term_op0 : val := λ: "x" "y",
  if: (Fst "x" < Fst "y") then #true
  else if: (Fst "x" = Fst "y") then
    if: Fst "x" = #0 (* Int *) then Snd "x" ≤ Snd "y"
    else leq_loc (Snd "x") (Snd "y") (* Nonce *)
  else #false.

Definition leq_key_type : val := λ: "x" "y",
  "x" ≤ "y".

Definition leq_term_op1 : val := λ: "x" "y",
  if: (Fst "x" < Fst "y") then #true
  else if: (Fst "x" = Fst "y") then
    if: Fst "x" = #0 (* Key *) then leq_key_type (Snd "x") (Snd "y")
    else #true (* Hash *)
  else #false.

Definition leq_term_op2 : val := λ: "x" "y",
  "x" ≤ "y".

Definition leq_term : val := rec: "loop" "t1" "t2" :=
 (if: (Fst "t1" < Fst "t2") then #true
  else if: (Fst "t1" = Fst "t2") then
    let: "tag" := Fst "t1" in
    let: "a1"  := Snd "t1" in
    let: "a2"  := Snd "t2" in
    if: "tag" = #TOp0_tag then
      let: "o1" := "a1" in
      let: "o2" := "a2" in
      leq_term_op0 "o1" "o2"
    else if: "tag" = #TOp1_tag then
      let: "o1" := Fst "a1" in
      let: "t1" := Snd "a1" in
      let: "o2" := Fst "a2" in
      let: "t2" := Snd "a2" in
      if: eq_term_op1 "o1" "o2" then "loop" "t1" "t2"
      else leq_term_op1 "o1" "o2"
    else if: "tag" = #TOp2_tag then
      let: "o1" := Fst (Fst "a1") in
      let: "t11" := Snd (Fst "a1") in
      let: "t12" := Snd "a1" in
      let: "o2" := Fst (Fst "a2") in
      let: "t21" := Snd (Fst "a2") in
      let: "t22" := Snd "a2" in
      if: eq_term_op2 "o1" "o2" then
        if: eq_term "t11" "t21" then "loop" "t12" "t22"
        else "loop" "t11" "t21"
      else leq_term_op2 "o1" "o2"
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
Implicit Types pt : PreTerm.pre_term.
Implicit Types v : val.
Implicit Types Ψ : val → iProp Σ.
Implicit Types N : namespace.

Lemma twp_eq_term_op0 E (o1 o2 : term_op0) :
  ⊢ WP (eq_term_op0 (repr o1) (repr o2)) @ E
    [{ v, ⌜v = #(bool_decide (o1 = o2))⌝}].
Proof.
case: o1 o2 => [n1|a1] [n2|a2] /=; wp_lam; wp_pures => //.
- iPureIntro. congr (# (LitBool _)). apply: bool_decide_ext.
  intuition congruence.
- iPureIntro. congr (# (LitBool _)). apply: bool_decide_ext.
  intuition congruence.
Qed.

Lemma twp_eq_key_type E (o1 o2 : key_type) :
  ⊢ WP (eq_key_type (repr o1) (repr o2)) @ E
    [{ v, ⌜v = #(bool_decide (o1 = o2))⌝}].
Proof.
case: o1 o2 => [] [] /=; wp_lam; wp_pures => //.
Qed.

Lemma twp_eq_term_op1 E (o1 o2 : term_op1) :
  ⊢ WP (eq_term_op1 (repr o1) (repr o2)) @ E
    [{ v, ⌜v = #(bool_decide (o1 = o2))⌝}].
Proof.
case: o1 o2 => [o1|] [o2|] /=; wp_lam; wp_pures => //.
iApply twp_wand; first wp_apply twp_eq_key_type.
iIntros (?) "->". iPureIntro.
congr (# (LitBool _)). apply: bool_decide_ext.
intuition congruence.
Qed.

Lemma twp_eq_term_op2 E (o1 o2 : term_op2) :
  ⊢ WP (eq_term_op2 (repr o1) (repr o2)) @ E
    [{ v, ⌜v = #(bool_decide (o1 = o2))⌝}].
Proof.
case: o1 o2 => [] [] /=; wp_lam; wp_pures => //.
Qed.

Lemma twp_eq_pre_term_aux E (pt1 pt2 : PreTerm.pre_term) :
  ⊢ WP (eq_term (repr pt1) (repr pt2)) @ E
       [{ v, ⌜v = #(bool_decide (pt1 = pt2))⌝ }].
Proof.
elim: pt1 pt2 => [o1|o1 t1 IH1|o1 t11 IH1 t12 IH2|t1 IHt1 ts1 IHts1];
case=> [o2|o2 t2|o2 t21 t22|t2 ts2]; wp_rec; wp_pures=> //.
- iApply twp_wand; first by wp_apply twp_eq_term_op0.
  iIntros (?) "->". iPureIntro; congr (# (LitBool _)).
  apply: bool_decide_ext; intuition congruence.
- wp_bind (eq_term_op1 _ _).
  iApply twp_wand; first by wp_apply twp_eq_term_op1.
  iIntros (?) "->". case: bool_decide_reflect=> e1.
  + wp_pures. iApply twp_wand; first by wp_apply IH1.
    iIntros (?) "->". iPureIntro; congr (# (LitBool _)).
    apply: bool_decide_ext; intuition congruence.
  + wp_pures; iPureIntro; congr (# (LitBool _)).
    rewrite bool_decide_false; congruence.
- wp_bind (eq_term_op2 _ _).
  iApply twp_wand; first by wp_apply twp_eq_term_op2.
  iIntros (?) "->". case: bool_decide_reflect=> e1; last first.
    wp_pures; iPureIntro; congr (# (LitBool _)).
    rewrite bool_decide_false; congruence.
  wp_pures. wp_bind (eq_term _ _).
  wp_apply twp_wand; first by wp_apply IH1.
  iIntros (?) "->". case: bool_decide_reflect=> e2.
    wp_pures. wp_bind (eq_term _ _).
    wp_apply twp_wand; first by wp_apply IH2.
    iIntros (?) "->". iPureIntro; congr (# (LitBool _)).
    by apply: bool_decide_ext; intuition congruence.
  wp_pures; iPureIntro; congr (# (LitBool _)).
  rewrite bool_decide_false; congruence.
- wp_bind (eq_term _ _); iApply twp_wand; first iApply IHt1.
  iIntros (?) "->"; case: bool_decide_reflect=> e1; wp_pures; last first.
    rewrite bool_decide_false //; congruence.
  rewrite -!repr_list_val.
  iApply (@twp_eq_list PreTerm.pre_term); last first.
    iPureIntro; congr (# (LitBool _)); apply: bool_decide_ext.
    rewrite e1; split; congruence.
  rewrite /=.
  elim: ts1 IHts1 {e1} => //= [|x1 ts1 IH].
    by move=> *; exfalso; set_solver.
  case=> IHx1 /IH IHts1 x1' x2' Ψ.
  rewrite elem_of_cons; case=> [->|x1'_in]; iIntros "post"; last first.
    by iApply IHts1.
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

Import ssrbool seq path.

Import ssreflect.eqtype ssreflect.order.

Lemma twp_leq_term_op0 E (o1 o2 : term_op0) :
  ⊢ WP (leq_term_op0 (repr o1) (repr o2)) @ E
    [{ v, ⌜v = #(o1 <= o2)%O⌝}].
Proof.
rewrite PreTerm.op0_leqE.
case: o1 o2 => [n1|a1] [n2|a2] /=; wp_lam; wp_pures => //.
- iPureIntro. congr (# (LitBool _)). symmetry.
  exact/(sameP (Z.leb_spec0 _ _))/bool_decide_reflect.
- by iApply twp_leq_loc.
Qed.

Lemma twp_leq_term_op1 E (o1 o2 : term_op1) :
  ⊢ WP (leq_term_op1 (repr o1) (repr o2)) @ E
    [{ v, ⌜v = #(o1 <= o2)%O⌝}].
Proof.
rewrite PreTerm.op1_leqE.
case: o1 o2 => [k1|] [k2|] /=; wp_lam; wp_pures => //.
wp_lam; wp_pures. iPureIntro.
by case: k1 k2 => [] [].
Qed.

Lemma twp_leq_term_op2 E (o1 o2 : term_op2) :
  ⊢ WP (leq_term_op2 (repr o1) (repr o2)) @ E
    [{ v, ⌜v = #(o1 <= o2)%O⌝}].
Proof. by case: o1 o2 => [] [] /=; wp_lam; wp_pures => //. Qed.

Lemma twp_leq_pre_term E (pt1 pt2 : PreTerm.pre_term) Ψ :
  Ψ #(pt1 <= pt2)%O ⊢
  WP (leq_term (repr pt1) (repr pt2)) @ E [{ Ψ }].
Proof.
elim: pt1 pt2 Ψ => [o1|o1 t1 IH1|o1 t11 IH1 t12 IH2|t1 IHt1 ts1 IHts1];
case => [o2|o2 t2|o2 t21 t22|t2 ts2] Ψ;
iIntros "post"; wp_rec; wp_pures; try by iApply "post".
- iApply twp_wand; first by wp_apply twp_leq_term_op0.
  iIntros "% ->". by rewrite PreTerm.leqE.
- rewrite PreTerm.leqE /=. wp_bind (eq_term_op1 _ _).
  iApply twp_wand; first by wp_apply twp_eq_term_op1.
  iIntros "% ->". rewrite eq_op_bool_decide.
  case: (o1 == o2); wp_pures; first by iApply IH1.
  iApply twp_wand. by iApply twp_leq_term_op1.
  by iIntros "% ->".
- rewrite PreTerm.leqE /=. wp_bind (eq_term_op2 _ _).
  iApply twp_wand; first by wp_apply twp_eq_term_op2.
  iIntros "% ->". rewrite eq_op_bool_decide.
  case: (o1 == o2); wp_pures; last first.
    iApply twp_wand. by iApply twp_leq_term_op2.
    by iIntros "% ->".
  wp_apply twp_eq_pre_term.
  rewrite eq_op_bool_decide.
  case: eq_op; wp_pures; first by iApply IH2.
  by iApply IH1.
- rewrite PreTerm.leqE /=; wp_bind (eq_term _ _).
  iApply twp_eq_pre_term; rewrite eq_op_bool_decide.
  case: eqP=> [->|neq]; wp_pures; last by iApply IHt1.
  rewrite -!repr_list_val; iApply twp_leq_list => //.
  + move=> pt1 pt2 Ψ'; iIntros "_ post".
    by iApply twp_eq_pre_term; rewrite eq_op_bool_decide; iApply "post".
  + move/foldr_in in IHts1.
    move=> ????; iIntros "_ post".
    by rewrite /=; iApply IHts1 => //; iApply "post".
  + by iIntros "_".
Qed.

End Proofs.
