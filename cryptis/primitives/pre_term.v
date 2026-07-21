(* These proofs take much longer to check than the rest of the
development. Since they don't have many dependencies, they are left in their own
file to avoid slowing down the compilation process. *)

From cryptis Require Import lib.
From mathcomp Require Import ssreflect.
From mathcomp Require all_order ssrbool eqtype seq path.
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
    else if: "tag" = #TMul_tag then
      eq_list "eq" (Snd "x") (Snd "y")
    else #false
  else #false)%V.

Definition leq_term_op0 : val := λ: "x" "y",
  if: (Fst "x" < Fst "y") then #true
  else if: (Fst "x" = Fst "y") then
    if: Fst "x" = #0 (* Int *) then Snd "x" ≤ Snd "y"
    else (Snd "x") ≤ (Snd "y") (* Nonce *)
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
    else if: "tag" = #TMul_tag then
      leq_list eq_term "loop" "a1" "a2"
    else #false
  else #false)%V.

(* TODO: Better names / separate file *)
Definition hl_base : val := λ: "pt",
    if: Fst "pt" = #TOp2_tag then
        if: Fst (Fst (Snd "pt")) = #TExp_tag then Snd (Fst (Snd "pt"))
        else "pt"
    else "pt".

Definition hl_factors : val := λ: "pt",
    if: Fst "pt" = #TMul_tag then Snd "pt"
    else "pt" :: NILV.

Definition hl_exps : val := λ: "pt",
    if: Fst "pt" = #TOp2_tag then
        if: Fst (Fst (Snd "pt")) = #TExp_tag then hl_factors (Snd (Snd "pt"))
        else NILV
    else NILV.

Definition hl_inv : val := λ: "pt",
    if: Fst "pt" = #TOp1_tag then
        if: Fst (Fst (Snd "pt")) = #TInv_tag then Snd (Snd "pt")
        else (#TOp1_tag, (#TInv_tag, #(), "pt"))
    else (#TOp1_tag, (#TInv_tag, #(), "pt")).

Definition hl_insert_exp : val := λ: "pt" "pts",
    if: mem_list eq_term (hl_inv "pt") "pts" then
        rem_list eq_term (hl_inv "pt") "pts"
    else "pt" :: "pts".

Definition hl_cancel_invs : val := λ: "exps", foldr_list hl_insert_exp [] "exps".

(* Collapse a sorted+canceled factor list into a product term:
   [] ↦ PTMul [] (identity), [t] ↦ t, otherwise PTMul list. *)
Definition hl_mk_mul : val := λ: "c",
    match: "c" with
      NONE => (#TMul_tag, NILV)
    | SOME "x" =>
        match: Snd "x" with
          NONE => Fst "x"
        | SOME <> => (#TMul_tag, "c")
        end
    end.

Definition hl_exp : val := λ: "b" "e",
    let: "c" :=
        insertion_sort leq_term
          (hl_cancel_invs (append_lists (hl_exps "b") (hl_factors "e"))) in
    let: "e'" := hl_mk_mul "c" in
    if: eq_term "e'" (#TMul_tag, NILV) then hl_base "b"
    else (#TOp2_tag, (#TExp_tag, hl_base "b", "e'")).

Definition texp : val := λ: "base" "exp",
    hl_exp "base" "exp".

(* Product of two terms: concatenate their factor lists, cancel matching
   inverses, sort, and collapse — mirrors [hl_exp] but without an exponent
   base. *)
Definition hl_mul : val := λ: "t1" "t2",
    hl_mk_mul (insertion_sort leq_term
                 (hl_cancel_invs (append_lists (hl_factors "t1") (hl_factors "t2")))).

(* Distributing inverse: invert each factor with [hl_inv], then re-fold with the
   product machinery.  This computes [PreTerm.inv] (not the raw [hl_inv], which
   only handles non-products). *)
Definition hl_inv_distr : val := λ: "t",
    hl_mk_mul (insertion_sort leq_term
                 (hl_cancel_invs (map_list hl_inv (hl_factors "t")))).

Section Proofs.

Context `{!heapGS Σ}.

Implicit Types E : coPset.
Implicit Types a : loc.
Implicit Types pt : PreTerm.pre_term.
Implicit Types v : val.
Implicit Types Ψ : val → iProp Σ.
Implicit Types N : namespace.

Lemma twp_eq_term_op0 E (o1 o2 : term_op0) :
  ⊢ WP (eq_term_op0 (repr o1) (repr o2)) @ E
    [{ v, ⌜v = #(bool_decide (o1 = o2))⌝}].
Proof.
case: o1 o2 => [n1|[a1]] [n2|[a2]] /=; wp_lam; wp_pures => //.
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
case: o1 o2 => [o1||] [o2||] /=. all: wp_lam; wp_pures => //.
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
elim: pt1 pt2 => [o1|o1 t1 IH1|o1 t11 IH1 t12 IH2|ts1 IHts1];
case=> [o2|o2 t2|o2 t21 t22|ts2]; wp_rec; wp_pures=> //.
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
- rewrite -!repr_list_val.
  iApply (@twp_eq_list PreTerm.pre_term); last first.
    iPureIntro; congr (# (LitBool _)); apply: bool_decide_ext.
    by split; congruence.
  elim: ts1 IHts1 => //= [|x1 ts1 IH].
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

#[warnings="-ambiguous-paths"]
Import all_order ssrbool boot.eqtype seq path.

Lemma twp_leq_term_op0 E (o1 o2 : term_op0) :
  ⊢ WP (leq_term_op0 (repr o1) (repr o2)) @ E
    [{ v, ⌜v = #(o1 <= o2)%O⌝}].
Proof.
rewrite PreTerm.op0_leqE.
case: o1 o2 => [n1|a1] [n2|a2] /=; wp_lam; wp_pures => //.
- iPureIntro. congr (# (LitBool _)). symmetry.
  exact/(sameP (Z.leb_spec0 _ _))/bool_decide_reflect.
- iPureIntro. congr (# (LitBool _)).
  suff H: (reflect (nonce_loc a1 ≤ₗ nonce_loc a2) (a1 <= a2)%O) by
    apply/(sameP (bool_decide_reflect _)).
  by apply Z.leb_spec0.
Qed.

Lemma twp_leq_term_op1 E (o1 o2 : term_op1) :
  ⊢ WP (leq_term_op1 (repr o1) (repr o2)) @ E
    [{ v, ⌜v = #(o1 <= o2)%O⌝}].
Proof.
rewrite PreTerm.op1_leqE.
case: o1 o2 => [k1||] [k2||] /=; wp_lam; wp_pures => //.
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
elim: pt1 pt2 Ψ => [o1|o1 t1 IH1|o1 t11 IH1 t12 IH2|ts1 IHts1];
case => [o2|o2 t2|o2 t21 t22|ts2] Ψ;
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
- rewrite PreTerm.leqE /=.
  rewrite -!repr_list_val; iApply twp_leq_list => //.
  + move=> pt1 pt2 Ψ'; iIntros "_ post".
    by iApply twp_eq_pre_term; rewrite eq_op_bool_decide; iApply "post".
  + move/foldr_in in IHts1.
    move=> ????; iIntros "_ post".
    by rewrite /=; iApply IHts1 => //; iApply "post".
  + by iIntros "_".
Qed.

Lemma twp_hl_base E (pt : PreTerm.pre_term) Ψ:
    Ψ (repr (PreTerm.base pt)) ⊢
    WP hl_base (repr pt) @ E [{ Ψ }].
Proof.
case: pt => [o|o t|o t1 t2|ts] /=; iIntros "HΨ"; wp_lam; wp_pures;
  try by iApply "HΨ".
by case: o => /=; wp_pures; iApply "HΨ".
Qed.

Lemma twp_hl_factors E (pt : PreTerm.pre_term) Ψ :
    Ψ (repr (PreTerm.factors pt)) ⊢
    WP hl_factors (repr pt) @ E [{ Ψ }].
Proof.
have reprS : forall pt' : PreTerm.pre_term,
    repr [:: pt'] = InjRV (repr pt', InjLV #()).
  by move=> pt'; rewrite repr_list_unseal.
rewrite /PreTerm.factors.
case: pt => [o|o t|o t1 t2|ts]; iIntros "HΨ"; wp_lam; wp_pures.
- rewrite /CONS; wp_pures; iEval (rewrite reprS /=) in "HΨ"; iApply "HΨ".
- rewrite /CONS; wp_pures; iEval (rewrite reprS /=) in "HΨ"; iApply "HΨ".
- rewrite /CONS; wp_pures; iEval (rewrite reprS /=) in "HΨ"; iApply "HΨ".
- rewrite -!repr_list_val; by iApply "HΨ".
Qed.

Lemma twp_hl_exps E (pt : PreTerm.pre_term) Ψ :
    Ψ (repr (PreTerm.exps pt)) ⊢
    WP hl_exps (repr pt) @ E [{ Ψ }].
Proof.
rewrite /PreTerm.exps /PreTerm.expo.
case: pt => [o|o t|o t1 t2|ts]; iIntros "HΨ"; wp_lam; wp_pures;
  try (by iEval (rewrite [PreTerm.factors _]/= repr_list_unseal /=) in "HΨ";
       iApply "HΨ").
case: o => /=; wp_pures;
  try (by iEval (rewrite repr_list_unseal /=) in "HΨ"; iApply "HΨ").
by wp_apply twp_hl_factors; iApply "HΨ".
Qed.

Lemma twp_hl_inv E (pt : PreTerm.pre_term) Ψ :
    Ψ (repr (PreTerm.inv_aux pt)) ⊢
    WP hl_inv (repr pt) @ E [{ Ψ }].
Proof.
    case: pt => [*|t *|*|*] /=; iIntros "HΨ";
        try case: t => * /=; wp_lam; wp_pures; iApply "HΨ".
Qed.

Lemma wp_hl_inv E (pt : PreTerm.pre_term) Ψ:
    Ψ (repr (PreTerm.inv_aux pt)) ⊢
    WP hl_inv (repr pt) @ E {{ Ψ }}.
Proof. iIntros "HΨ"; iApply twp_wp; by wp_apply twp_hl_inv. Qed.

Lemma twp_hl_insert_factor E pt (pts : seq PreTerm.pre_term) Φ :
    Φ (repr (PreTerm.insert_factor pt pts)) ⊢
    WP hl_insert_exp (repr pt) (repr pts) @ E [{ Φ }].
Proof.
    iIntros "HΦ".
    rewrite /PreTerm.insert_factor.
    wp_lam; wp_pures.
    wp_apply twp_hl_inv.
    wp_apply twp_mem_list => //.
        iIntros "%x %y %Ψ _ HΨ". wp_apply twp_eq_pre_term.
        rewrite eq_op_bool_decide. by iApply "HΨ".
        iIntros "_".
    case: (PreTerm.inv_aux pt \in pts); wp_pures.
        - wp_apply twp_hl_inv.
          wp_apply twp_rem_list => //.
          iIntros "%x %y %Ψ _ HΨ". wp_apply twp_eq_pre_term.
          rewrite eq_op_bool_decide. by iApply "HΨ".
          iIntros "_". iApply "HΦ".
        - wp_apply twp_cons. iApply "HΦ".
Qed.

Lemma twp_hl_cancel_invs E (pts : seq PreTerm.pre_term) Φ :
    Φ (repr (PreTerm.cancel_invs pts)) ⊢
    WP hl_cancel_invs (repr pts) @ E [{ Φ }].
Proof.
    iIntros "HΦ"; wp_lam; wp_pures.
    wp_apply twp_nil.
    wp_apply twp_foldr_list => //.
    iIntros "%a %b %Ψ _ HΨ".
        wp_apply twp_hl_insert_factor.
        by iApply "HΨ".
    iIntros "_". iApply "HΦ".
Qed.

Lemma twp_hl_mk_mul E (c : seq PreTerm.pre_term) Ψ :
    Ψ (repr (match c with [:: t] => t | _ => PreTerm.PTMul c end)) ⊢
    WP hl_mk_mul (repr c) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam.
case: c => [|t [|u c']].
- rewrite {1}repr_list_unseal /=; wp_pures.
  rewrite (_ : (#TMul_tag, NILV)%V = repr (PreTerm.PTMul [::])); last first.
    by rewrite /= repr_list_unseal.
  by iApply "HΨ".
- rewrite {1}repr_list_unseal /=; wp_pures. by iApply "HΨ".
- rewrite {1}repr_list_unseal /=; wp_pures.
  rewrite [repr_list [:: t, u & c']]repr_list_val; by iApply "HΨ".
Qed.

Lemma twp_hl_exp E (b e : PreTerm.pre_term) Φ :
    Φ (repr (PreTerm.exp b e)) ⊢
    WP hl_exp (repr b) (repr e) @ E [{ Φ }].
Proof.
iIntros "HΦ"; wp_lam; wp_pures.
wp_apply twp_hl_factors.
wp_apply twp_hl_exps.
wp_apply twp_append_lists.
wp_apply twp_hl_cancel_invs.
wp_apply twp_insertion_sort => //.
  iIntros "%x %y %Ψ _ HΨ". iApply twp_leq_pre_term. by iApply "HΨ".
iIntros "_".
rewrite (_ : (PreTerm.exps b ++ PreTerm.factors e)%list =
             flatten (map PreTerm.factors [:: PreTerm.expo b; e]));
  last by rewrite /PreTerm.exps /= cats0.
wp_pures.
wp_apply twp_hl_mk_mul.
wp_pures.
rewrite (_ : (#TMul_tag, NILV)%V = repr (PreTerm.PTMul [::])); last first.
  by rewrite /= repr_list_unseal.
wp_bind (eq_term _ _); iApply twp_eq_pre_term.
set c := (sort <=%O (PreTerm.cancel_invs
  (PreTerm.factors (PreTerm.expo b) ++ PreTerm.factors e ++ [::]))).
have Emul : PreTerm.mul [:: PreTerm.expo b; e] =
   match c with
   | [::] => PreTerm.PTMul c | [:: t] => t | [:: t, _ & _] => PreTerm.PTMul c
   end.
  by rewrite /PreTerm.mul /= -/c; case: (c) => [|? []].
rewrite -!Emul.
case: bool_decide_reflect => [HM|HM]; wp_pures.
- wp_apply twp_hl_base.
  have -> : PreTerm.exp b e = PreTerm.base b.
    by rewrite /PreTerm.exp HM eqxx.
  by iApply "HΦ".
- wp_apply twp_hl_base. wp_pures.
  have -> : PreTerm.exp b e =
            PreTerm.PTExp (PreTerm.base b) (PreTerm.mul [:: PreTerm.expo b; e]).
    by rewrite /PreTerm.exp (introF eqP HM).
  by iApply "HΦ".
Qed.

Lemma twp_hl_mul E (pt1 pt2 : PreTerm.pre_term) Φ :
    Φ (repr (PreTerm.mul [:: pt1; pt2])) ⊢
    WP hl_mul (repr pt1) (repr pt2) @ E [{ Φ }].
Proof.
iIntros "HΦ"; wp_lam; wp_pures.
wp_apply twp_hl_factors.
wp_apply twp_hl_factors.
wp_apply twp_append_lists.
wp_apply twp_hl_cancel_invs.
wp_apply twp_insertion_sort => //.
  iIntros "%x %y %Ψ _ HΨ". iApply twp_leq_pre_term. by iApply "HΨ".
iIntros "_".
wp_apply twp_hl_mk_mul.
set c := sort <=%O (PreTerm.cancel_invs (PreTerm.factors pt1 ++ PreTerm.factors pt2)).
have Emul : PreTerm.mul [:: pt1; pt2] =
   match c with
   | [::] => PreTerm.PTMul c | [:: t] => t | [:: t, _ & _] => PreTerm.PTMul c
   end.
  by rewrite /PreTerm.mul /= cats0 -/c; case: (c) => [|? []].
rewrite -Emul.
by iApply "HΦ".
Qed.

Lemma twp_hl_inv_spec E (pt : PreTerm.pre_term) :
    [[{ True }]] hl_inv (repr pt) @ E [[{ RET repr (PreTerm.inv_aux pt); True }]].
Proof. iIntros (Φ) "_ HΦ". iApply twp_hl_inv. by iApply "HΦ". Qed.

Lemma twp_hl_inv_distr E (pt : PreTerm.pre_term) Φ
    (wf : is_true (PreTerm.wf_term pt)) :
    Φ (repr (PreTerm.inv pt)) ⊢
    WP hl_inv_distr (repr pt) @ E [{ Φ }].
Proof.
iIntros "HΦ"; wp_lam; wp_pures.
wp_apply twp_hl_factors.
wp_apply (twp_map_list PreTerm.inv_aux hl_inv).
- apply/Forall_forall => x _. exact: twp_hl_inv_spec.
- done.
- iIntros "_".
  wp_apply twp_hl_cancel_invs.
  wp_apply twp_insertion_sort => //.
    iIntros "%x %y %Ψ _ HΨ". iApply twp_leq_pre_term. by iApply "HΨ".
  iIntros "_".
  wp_apply twp_hl_mk_mul.
  have mapE : ListDef.map PreTerm.inv_aux (PreTerm.factors pt)
            = seq.map PreTerm.inv_aux (PreTerm.factors pt).
    by elim: (PreTerm.factors pt) => //= ? ? ->.
  rewrite mapE.
  have Nm : all (fun t => ~~ PreTerm.is_mul t)
              (seq.map PreTerm.inv_aux (PreTerm.factors pt)).
    move: (PreTerm.wf_factors wf). elim: (PreTerm.factors pt) => [_ //|t l IH] /=.
    move=> /andP[wft wfl]. rewrite (PreTerm.is_mul_inv_aux wft). exact: (IH wfl).
  set c := sort <=%O
             (PreTerm.cancel_invs (seq.map PreTerm.inv_aux (PreTerm.factors pt))).
  have HE : PreTerm.inv pt =
     match c with
     | [::] => PreTerm.PTMul c | [:: t] => t | [:: t, _ & _] => PreTerm.PTMul c end.
    rewrite (PreTerm.inv_factors wf) /PreTerm.mul
            (PreTerm.flatten_factors_Nmul_id (proj2 (is_trueP _) Nm)) -/c.
    by case: (c) => [|? []].
  rewrite -HE. by iApply "HΦ".
Qed.

End Proofs.
