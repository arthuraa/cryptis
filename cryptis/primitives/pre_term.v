(* HeapLang implementations of the pre-term operations behind
   [primitives/comp.v], with specs saying that each program computes the
   corresponding function of [core/pre_term].

   Pre-terms are trees ([val_of_pre_term]).  [cmp_term] compares two of them
   in the order derived in [core/pre_term/base.v] ([pt_cmpE]); [eq_term] and
   [leq_term] are its equality and order tests.  The operations normalize by
   evaluation, as [PreTerm.normalize] does: they read their arguments as
   fractions ([hl_frac_of]) or Diffie-Hellman maps ([hl_dh_map]), compute with
   the operations of [primitives/frac.v] and [primitives/fmap.v], and encode
   the result as a tree ([hl_mod_of_frac], [hl_dh_of]). *)

From mathcomp Require Import ssreflect.
From mathcomp Require Import order.
From mathcomp Require eqtype ssrbool.
From stdpp Require Import list sorting.
From iris.heap_lang Require Import notation proofmode.
From cryptis.lib Require Import repr list list_sort fmap mset sms.
From cryptis.lib Require Import poly poly_gcd frac.
From cryptis.core Require Import pre_term.
From cryptis.primitives Require Import mset sms fmap poly frac.

Unset Printing Implicit Defensive.

(** ** The derived order as a comparison *)

Definition cmp_Z (c : comparison) : Z :=
  match c with Lt => -1 | Eq => 0 | Gt => 1 end.

Definition tag_of_op0 (o : term_op0) : Z :=
  match o with
  | O0Int _ => TInt_tag
  | O0Nonce _ => TNonce_tag
  | O0Zero => TZero_tag
  | O0One => TOne_tag
  | O0GOne => TGOne_tag
  end.

Definition tag_of_op1 (o : term_op1) : Z :=
  match o with
  | O1Key _ => TKey_tag
  | O1Hash => THash_tag
  | O1Opp => TOpp_tag
  | O1Inv => TInv_tag
  | O1GInv => TGInv_tag
  end.

Section Order.
#[warnings="-ambiguous-paths"]
Import Order.POrderTheory Order.TotalTheory ssrbool boot.eqtype.
Open Scope order_scope.

Definition cmp_ord {d} {T : orderType d} (x y : T) : comparison :=
  if x <= y then if y <= x then Eq else Lt else Gt.

Lemma cmp_ord_refl {d} {T : orderType d} (x : T) : cmp_ord x x = Eq.
Proof. by rewrite /cmp_ord lexx. Qed.

Lemma cmp_ord_eq {d} {T : orderType d} (x y : T) : cmp_ord x y = Eq ↔ x = y.
Proof.
split; last by move=> ->; exact: cmp_ord_refl.
rewrite /cmp_ord; case: ifP => // xy; case: ifP => // yx _.
by apply/eqP; rewrite eq_le xy yx.
Qed.

Lemma cmp_ord_Gt {d} {T : orderType d} (x y : T) :
  cmp_ord x y = Gt ↔ (x <= y) = false.
Proof. by rewrite /cmp_ord; case: (x <= y) => //; case: (y <= x). Qed.

#[local] Lemma le_alt d (T : orderType d) (x y : T) :
  (x <= y) = if x == y then true else (x <= y).
Proof. by case: (ltgtP x y). Qed.

Lemma cmp_ord_Z (n1 n2 : Z) : cmp_ord n1 n2 = Z.compare n1 n2.
Proof.
rewrite /cmp_ord; case: (Z.compare_spec n1 n2) => [->|lt|gt].
- by rewrite lexx.
- have -> : (n1 <= n2) = true by apply/Z.leb_le; lia.
  by have -> : (n2 <= n1) = false by apply/Z.leb_nle; lia.
- by have -> : (n1 <= n2) = false by apply/Z.leb_nle; lia.
Qed.

Lemma op0_leqE (o1 o2 : term_op0) :
  (o1 <= o2) =
  match o1, o2 with
  | O0Int n1, O0Int n2 => n1 <= n2
  | O0Nonce a1, O0Nonce a2 => a1 <= a2
  | _, _ => (tag_of_op0 o1 <=? tag_of_op0 o2)%Z
  end.
Proof.
by case: o1 o2 => [n1|a1| | |] [n2|a2| | |] //=; rewrite [RHS]le_alt.
Qed.

Lemma cmp_op0E (o1 o2 : term_op0) :
  cmp_ord o1 o2 =
  match o1, o2 with
  | O0Int n1, O0Int n2 => Z.compare n1 n2
  | O0Nonce a1, O0Nonce a2 =>
    Z.compare (locations.loc_car (nonce_loc a1))
              (locations.loc_car (nonce_loc a2))
  | _, _ => Z.compare (tag_of_op0 o1) (tag_of_op0 o2)
  end.
Proof.
rewrite /cmp_ord !op0_leqE.
by case: o1 o2 => [n1|[l1]| | |] [n2|[l2]| | |] //; rewrite -cmp_ord_Z.
Qed.

Lemma cmp_ord_key_type (k1 k2 : key_type) :
  cmp_ord k1 k2 = Z.compare (int_of_key_type k1) (int_of_key_type k2).
Proof. by case: k1; case: k2. Qed.

Lemma op1_leqE (o1 o2 : term_op1) :
  (o1 <= o2) =
  match o1, o2 with
  | O1Key k1, O1Key k2 => k1 <= k2
  | _, _ => (tag_of_op1 o1 <=? tag_of_op1 o2)%Z
  end.
Proof. by case: o1 o2 => [k1| | | |] [k2| | | |] //=; rewrite [RHS]le_alt. Qed.

Lemma cmp_op1E (o1 o2 : term_op1) :
  cmp_ord o1 o2 =
  match o1, o2 with
  | O1Key k1, O1Key k2 => Z.compare (int_of_key_type k1) (int_of_key_type k2)
  | _, _ => Z.compare (tag_of_op1 o1) (tag_of_op1 o2)
  end.
Proof.
rewrite /cmp_ord !op1_leqE.
by case: o1 o2 => [k1| | | |] [k2| | | |] //; rewrite -cmp_ord_key_type.
Qed.

Lemma cmp_op2E (o1 o2 : term_op2) :
  cmp_ord o1 o2 = Z.compare (int_of_term_op2 o1) (int_of_term_op2 o2).
Proof. by case: o1; case: o2. Qed.

(** The comparison of distinct operators decides; equal operators defer to
    the next argument. *)
#[local] Lemma cmp_ord_lex {d} {T : orderType d} (o1 o2 : T) (b12 b21 : bool) :
  (if (if o1 == o2 then b12 else o1 <= o2) then
     if (if o2 == o1 then b21 else o2 <= o1) then Eq else Lt
   else Gt) =
  match cmp_ord o1 o2 with
  | Eq => if b12 then if b21 then Eq else Lt else Gt
  | r => r
  end.
Proof.
case: (eqVneq o1 o2) => [<-|ne]; first by rewrite cmp_ord_refl.
rewrite /= -/(cmp_ord o1 o2).
by case E: (cmp_ord o1 o2) => //; move/cmp_ord_eq: E => e; rewrite e eqxx in ne.
Qed.

Lemma pt_cmpE (x y : PreTerm.pre_term) :
  cmp_ord x y =
  match x, y with
  | PreTerm.PT0 o1, PreTerm.PT0 o2 => cmp_ord o1 o2
  | PreTerm.PT1 o1 t1, PreTerm.PT1 o2 t2 =>
    match cmp_ord o1 o2 with Eq => cmp_ord t1 t2 | r => r end
  | PreTerm.PT2 o1 a1 b1, PreTerm.PT2 o2 a2 b2 =>
    match cmp_ord o1 o2 with
    | Eq => match cmp_ord a1 a2 with Eq => cmp_ord b1 b2 | r => r end
    | r => r
    end
  | _, _ => Z.compare (PreTerm.cons_num x) (PreTerm.cons_num y)
  end.
Proof.
rewrite {1}/cmp_ord (PreTerm.leqE x y) (PreTerm.leqE y x).
case: x y => [o1|o1 t1|o1 a1 b1] [o2|o2 t2|o2 a2 b2] //=.
- by rewrite cmp_ord_lex.
- by rewrite cmp_ord_lex; case: (cmp_ord o1 o2) => //; rewrite cmp_ord_lex.
Qed.

End Order.

(** ** Comparison *)

(* Three-way comparison of two integers or of two locations. *)
Definition cmp_lit : val := λ: "x" "y",
  if: "x" = "y" then #0 else if: "x" < "y" then #(-1) else #1.

Definition cmp_op0 : val := λ: "x" "y",
  if: Fst "x" = Fst "y" then cmp_lit (Snd "x") (Snd "y")
  else cmp_lit (Fst "x") (Fst "y").

Definition cmp_op1 : val := λ: "x" "y",
  if: Fst "x" = Fst "y" then
    if: Fst "x" = #TKey_tag then cmp_lit (Snd "x") (Snd "y") else #0
  else cmp_lit (Fst "x") (Fst "y").

Definition cmp_op2 : val := λ: "x" "y", cmp_lit "x" "y".

Definition cmp_term : val := rec: "cmp" "x" "y" :=
  let: "tx" := Fst "x" in
  let: "ty" := Fst "y" in
  if: "tx" = "ty" then
    let: "a" := Snd "x" in
    let: "b" := Snd "y" in
    if: "tx" = #TOp0_tag then cmp_op0 "a" "b"
    else if: "tx" = #TOp1_tag then
      let: "r" := cmp_op1 (Fst "a") (Fst "b") in
      if: "r" = #0 then "cmp" (Snd "a") (Snd "b") else "r"
    else
      let: "r" := cmp_op2 (Fst (Fst "a")) (Fst (Fst "b")) in
      if: "r" = #0 then
        let: "r" := "cmp" (Snd (Fst "a")) (Snd (Fst "b")) in
        if: "r" = #0 then "cmp" (Snd "a") (Snd "b") else "r"
      else "r"
  else cmp_lit "tx" "ty".

Definition eq_term : val := λ: "x" "y", cmp_term "x" "y" = #0.

Definition leq_term : val := λ: "x" "y", ~ (cmp_term "x" "y" = #1).

(** ** Exponents and group elements *)

Definition eq_frac : val := λ: "f" "g", frac_eq eq_term "f" "g".

Definition add_frac : val := λ: "f" "g", frac_add eq_term leq_term "f" "g".

Definition mul_frac : val := λ: "f" "g", frac_mul eq_term leq_term "f" "g".

Definition inv_frac : val := λ: "f", frac_inv eq_term leq_term "f".

Definition is_one_frac : val := λ: "f", frac_eq eq_term "f" frac_one.

Definition hl_mk1 (o : term_op1) : val := λ: "t", (#TOp1_tag, (repr o, "t")).

Definition hl_mk2 (o : term_op2) : val := λ: "t1" "t2",
  (#TOp2_tag, (repr o, "t1", "t2")).

Definition hl_frac_of : val := rec: "go" "pt" :=
  let: "a" := Snd "pt" in
  if: Fst "pt" = #TOp0_tag then
    if: Fst "a" = #TZero_tag then frac_zero
    else if: Fst "a" = #TOne_tag then frac_one
    else frac_var "pt"
  else if: Fst "pt" = #TOp1_tag then
    if: Fst (Fst "a") = #TOpp_tag then frac_opp ("go" (Snd "a"))
    else if: Fst (Fst "a") = #TInv_tag then inv_frac ("go" (Snd "a"))
    else frac_var "pt"
  else
    if: Fst (Fst "a") = #TAdd_tag then
      add_frac ("go" (Snd (Fst "a"))) ("go" (Snd "a"))
    else if: Fst (Fst "a") = #TMul_tag then
      mul_frac ("go" (Snd (Fst "a"))) ("go" (Snd "a"))
    else frac_var "pt".

Definition hl_dh_add : val := λ: "m1" "m2",
  fmap_merge eq_term leq_term eq_frac add_frac frac_zero frac_zero "m1" "m2".

Definition hl_dh_opp : val := λ: "m", fmap_map eq_frac frac_opp frac_zero "m".

Definition hl_dh_scale : val := λ: "r" "m",
  fmap_map eq_frac (λ: "f", mul_frac "f" "r") frac_zero "m".

Definition hl_dh_map : val := rec: "go" "pt" :=
  let: "a" := Snd "pt" in
  if: if: Fst "pt" = #TOp0_tag then Fst "a" = #TGOne_tag else #false then
    fmap_empty
  else if: if: Fst "pt" = #TOp1_tag then Fst (Fst "a") = #TGInv_tag
           else #false then
    hl_dh_opp ("go" (Snd "a"))
  else if: if: Fst "pt" = #TOp2_tag then Fst (Fst "a") = #TGMul_tag
           else #false then
    hl_dh_add ("go" (Snd (Fst "a"))) ("go" (Snd "a"))
  else if: if: Fst "pt" = #TOp2_tag then Fst (Fst "a") = #TExp_tag
           else #false then
    hl_dh_scale (hl_frac_of (Snd "a")) ("go" (Snd (Fst "a")))
  else fmap_singleton eq_frac frac_zero "pt" frac_one.

Definition hl_fold_tree_ne : val := rec: "go" "op" "t" "l" :=
  match: "l" with
    NONE => "t"
  | SOME "p" => "op" "t" ("go" "op" (Fst "p") (Snd "p"))
  end.

Definition hl_fold_tree : val := λ: "op" "unit" "l",
  match: "l" with
    NONE => "unit"
  | SOME "p" => hl_fold_tree_ne "op" (Fst "p") (Snd "p")
  end.

Definition hl_one : val := (#TOp0_tag, (#TOne_tag, #())).

Definition hl_zero : val := (#TOp0_tag, (#TZero_tag, #())).

Definition hl_gone : val := (#TOp0_tag, (#TGOne_tag, #())).

Definition hl_encode_mono : val := λ: "M",
  hl_fold_tree (hl_mk2 O2Mul) hl_one "M".

Definition hl_encode_sum : val := λ: "Ms",
  hl_fold_tree (hl_mk2 O2Add) hl_zero (map_list hl_encode_mono "Ms").

Definition hl_is_nil : val := λ: "l",
  match: "l" with NONE => #true | SOME <> => #false end.

Definition hl_encode_poly : val := λ: "p",
  if: hl_is_nil (Snd "p") then hl_encode_sum (Fst "p")
  else if: hl_is_nil (Fst "p") then hl_mk1 O1Opp (hl_encode_sum (Snd "p"))
  else hl_mk2 O2Add (hl_encode_sum (Fst "p"))
         (hl_mk1 O1Opp (hl_encode_sum (Snd "p"))).

Definition hl_mod_of_frac : val := λ: "r",
  if: poly_eq eq_term (Snd "r") poly_one then hl_encode_poly (Fst "r")
  else hl_mk2 O2Mul (hl_encode_poly (Fst "r"))
         (hl_mk1 O1Inv (hl_encode_poly (Snd "r"))).

Definition hl_mk_exp : val := λ: "b" "r",
  if: is_one_frac "r" then "b" else hl_mk2 O2Exp "b" (hl_mod_of_frac "r").

Definition hl_dh_of : val := λ: "m",
  hl_fold_tree (hl_mk2 O2GMul) hl_gone
    (map_list (λ: "e", hl_mk_exp (Fst "e") (Snd "e")) "m").

Definition hl_mul : val := λ: "t1" "t2",
  hl_mod_of_frac (mul_frac (hl_frac_of "t1") (hl_frac_of "t2")).

Definition hl_inv : val := λ: "t", hl_mod_of_frac (inv_frac (hl_frac_of "t")).

Definition hl_sum : val := λ: "t1" "t2",
  hl_mod_of_frac (add_frac (hl_frac_of "t1") (hl_frac_of "t2")).

Definition hl_opp : val := λ: "t", hl_mod_of_frac (frac_opp (hl_frac_of "t")).

Definition hl_gmul : val := λ: "t1" "t2",
  hl_dh_of (hl_dh_add (hl_dh_map "t1") (hl_dh_map "t2")).

Definition hl_ginv : val := λ: "t", hl_dh_of (hl_dh_opp (hl_dh_map "t")).

Definition hl_exp : val := λ: "b" "e",
  hl_dh_of (hl_dh_scale (hl_frac_of "e") (hl_dh_map "b")).

Definition texp : val := λ: "base" "exp", hl_exp "base" "exp".

(** ** Pure facts *)

Section Proofs.

Context `{!heapGS Σ}.

Implicit Types E : coPset.
Implicit Types (x y pt : PreTerm.pre_term).
Implicit Types Ψ : val → iProp Σ.

(** *** Comparison *)

Lemma twp_cmp_lit_int (n1 n2 : Z) E Ψ :
  Ψ #(cmp_Z (Z.compare n1 n2)) ⊢ WP cmp_lit #n1 #n2 @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam; wp_pures.
case: (Z.compare_spec n1 n2) => [->|lt|gt].
- by rewrite bool_decide_eq_true_2 //; wp_pures.
- rewrite bool_decide_eq_false_2; last by move=> [=]; lia.
  wp_pures; rewrite bool_decide_eq_true_2 //.
  by wp_pures.
- rewrite bool_decide_eq_false_2; last by move=> [=]; lia.
  wp_pures; rewrite bool_decide_eq_false_2; last lia.
  by wp_pures.
Qed.

Lemma twp_cmp_lit_loc (l1 l2 : loc) E Ψ :
  Ψ #(cmp_Z (Z.compare (loc_car l1) (loc_car l2))) ⊢
  WP cmp_lit #l1 #l2 @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam; wp_pures.
case: (Z.compare_spec (loc_car l1) (loc_car l2)) => [e|lt|gt].
- have -> : l1 = l2 by case: l1 l2 e => [z1] [z2] /= ->.
  by rewrite bool_decide_eq_true_2 //; wp_pures.
- rewrite bool_decide_eq_false_2;
    last by move=> [=] e; move: lt; rewrite e; lia.
  wp_pures; rewrite bool_decide_eq_true_2 //.
  by wp_pures.
- rewrite bool_decide_eq_false_2;
    last by move=> [=] e; move: gt; rewrite e; lia.
  wp_pures; rewrite bool_decide_eq_false_2; last by rewrite /Loc.lt; lia.
  by wp_pures.
Qed.

Lemma twp_cmp_lit_unit E Ψ :
  Ψ #(cmp_Z Eq) ⊢ WP cmp_lit #() #() @ E [{ Ψ }].
Proof. by iIntros "HΨ"; wp_lam; wp_pures. Qed.

Lemma twp_cmp_op0 (o1 o2 : term_op0) E Ψ :
  Ψ #(cmp_Z (cmp_ord o1 o2)) ⊢
  WP cmp_op0 (repr o1) (repr o2) @ E [{ Ψ }].
Proof.
rewrite cmp_op0E.
case: o1 o2 => [n1|[l1]| | |] [n2|[l2]| | |] /=; iIntros "HΨ"; wp_lam;
  wp_pures; try by wp_apply twp_cmp_lit_int.
- by wp_apply twp_cmp_lit_loc.
- by wp_apply twp_cmp_lit_unit.
- by wp_apply twp_cmp_lit_unit.
- by wp_apply twp_cmp_lit_unit.
Qed.

Lemma twp_cmp_op1 (o1 o2 : term_op1) E Ψ :
  Ψ #(cmp_Z (cmp_ord o1 o2)) ⊢
  WP cmp_op1 (repr o1) (repr o2) @ E [{ Ψ }].
Proof.
rewrite cmp_op1E.
by case: o1 o2 => [k1| | | |] [k2| | | |] /=; iIntros "HΨ"; wp_lam; wp_pures;
  try wp_apply twp_cmp_lit_int.
Qed.

Lemma twp_cmp_op2 (o1 o2 : term_op2) E Ψ :
  Ψ #(cmp_Z (cmp_ord o1 o2)) ⊢
  WP cmp_op2 (repr o1) (repr o2) @ E [{ Ψ }].
Proof.
rewrite cmp_op2E.
by iIntros "HΨ"; wp_lam; wp_pures; wp_apply twp_cmp_lit_int.
Qed.

Lemma twp_cmp_term x y E Ψ :
  Ψ #(cmp_Z (cmp_ord x y)) ⊢ WP cmp_term (repr x) (repr y) @ E [{ Ψ }].
Proof.
elim: x y E Ψ => [o1|o1 t1 IH|o1 a1 IHa b1 IHb] [o2|o2 t2|o2 a2 b2] E Ψ;
  rewrite pt_cmpE /=; iIntros "HΨ"; wp_rec; wp_pures;
  try by wp_apply twp_cmp_lit_int.
- by wp_apply twp_cmp_op0.
- wp_apply twp_cmp_op1; case: (cmp_ord o1 o2) => /=; wp_pures.
  + by iApply IH.
  + by iApply "HΨ".
  + by iApply "HΨ".
- wp_apply twp_cmp_op2; case: (cmp_ord o1 o2) => /=; wp_pures.
  + wp_apply IHa; case: (cmp_ord a1 a2) => /=; wp_pures.
    * by iApply IHb.
    * by iApply "HΨ".
    * by iApply "HΨ".
  + by iApply "HΨ".
  + by iApply "HΨ".
Qed.

Lemma twp_eq_pre_term x y E Ψ :
  Ψ #(bool_decide (x = y)) ⊢ WP eq_term (repr x) (repr y) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam; wp_pures; wp_apply twp_cmp_term; wp_pures.
have -> : bool_decide (#(cmp_Z (cmp_ord x y)) = #0) = bool_decide (x = y).
  apply: bool_decide_ext; rewrite -cmp_ord_eq.
  by case: (cmp_ord x y); split=> // - [].
by [].
Qed.

Lemma twp_leq_pre_term x y E Ψ :
  Ψ #(bool_decide (MSet.le x y)) ⊢ WP leq_term (repr x) (repr y) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam; wp_pures; wp_apply twp_cmp_term; wp_pures.
have -> : negb (bool_decide (#(cmp_Z (cmp_ord x y)) = #1)) =
          bool_decide (MSet.le x y).
  have -> : bool_decide (MSet.le x y) = bool_decide (pt_order x y).
    by apply: bool_decide_ext; rewrite pt_order_lexico.
  rewrite bool_decide_pt_order.
  case C: (cmp_ord x y).
  - by move/cmp_ord_eq: C => ->; rewrite Order.POrderTheory.lexx.
  - by move: C; rewrite /cmp_ord; case: (x <= y)%O => //; case: (y <= x)%O.
  - by move/cmp_ord_Gt: C => ->.
by [].
Qed.

(** *** Fractions *)

Lemma twp_eq_frac (f g : Frac.frac PreTerm.pre_term) E Ψ :
  Ψ #(bool_decide (f = g)) ⊢ WP eq_frac (repr f) (repr g) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam; wp_pures.
by wp_apply (twp_frac_eq eq_term twp_eq_pre_term).
Qed.

Lemma twp_add_frac (f g : Frac.frac PreTerm.pre_term) E Ψ :
  Ψ (repr (Frac.add f g)) ⊢ WP add_frac (repr f) (repr g) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam; wp_pures.
by wp_apply (twp_frac_add eq_term leq_term twp_eq_pre_term twp_leq_pre_term).
Qed.

Lemma twp_mul_frac (f g : Frac.frac PreTerm.pre_term) E Ψ :
  Ψ (repr (Frac.mul f g)) ⊢ WP mul_frac (repr f) (repr g) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam; wp_pures.
by wp_apply (twp_frac_mul eq_term leq_term twp_eq_pre_term twp_leq_pre_term).
Qed.

Lemma twp_inv_frac (f : Frac.frac PreTerm.pre_term) E Ψ :
  Ψ (repr (Frac.inv f)) ⊢ WP inv_frac (repr f) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam.
by wp_apply (twp_frac_inv eq_term leq_term twp_eq_pre_term twp_leq_pre_term).
Qed.

Lemma twp_is_one_frac (f : Frac.frac PreTerm.pre_term) E Ψ :
  Ψ #(bool_decide (f = Frac.one)) ⊢ WP is_one_frac (repr f) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam; rewrite -(repr_frac_one (T := PreTerm.pre_term)).
by wp_apply (twp_frac_eq eq_term twp_eq_pre_term).
Qed.

(** *** Readings *)

Lemma twp_hl_mk1 o pt E Ψ :
  Ψ (repr (PreTerm.PT1 o pt)) ⊢ WP hl_mk1 o (repr pt) @ E [{ Ψ }].
Proof. by iIntros "HΨ"; wp_lam; wp_pures. Qed.

Lemma twp_hl_mk2 o pt1 pt2 E Ψ :
  Ψ (repr (PreTerm.PT2 o pt1 pt2)) ⊢
  WP hl_mk2 o (repr pt1) (repr pt2) @ E [{ Ψ }].
Proof. by iIntros "HΨ"; wp_lam; wp_pures. Qed.

Lemma twp_hl_frac_atom pt E Ψ :
  Ψ (repr (PreTerm.fvar pt)) ⊢ WP frac_var (repr pt) @ E [{ Ψ }].
Proof. by rewrite /PreTerm.fvar -Frac.varE; exact: twp_frac_var. Qed.

Lemma twp_hl_frac_of pt E Ψ :
  Ψ (repr (PreTerm.frac_of pt)) ⊢ WP hl_frac_of (repr pt) @ E [{ Ψ }].
Proof.
elim: pt E Ψ => [o|o t IH|o t1 IH1 t2 IH2] E Ψ; iIntros "HΨ"; wp_rec.
- case: o => [n|a| | |]; wp_pures.
  + by wp_apply (twp_hl_frac_atom (PreTerm.PT0 (O0Int n))).
  + by wp_apply (twp_hl_frac_atom (PreTerm.PT0 (O0Nonce a))).
  + by rewrite -(repr_frac_zero (T := PreTerm.pre_term)); iApply "HΨ".
  + by rewrite -(repr_frac_one (T := PreTerm.pre_term)); iApply "HΨ".
  + by wp_apply (twp_hl_frac_atom (PreTerm.PT0 O0GOne)).
- case: o => [kt| | | |]; wp_pures.
  + by wp_apply (twp_hl_frac_atom (PreTerm.PT1 (O1Key kt) t)).
  + by wp_apply (twp_hl_frac_atom (PreTerm.PT1 O1Hash t)).
  + by wp_apply IH; wp_apply twp_frac_opp.
  + by wp_apply IH; wp_apply twp_inv_frac.
  + by wp_apply (twp_hl_frac_atom (PreTerm.PT1 O1GInv t)).
- case: o; wp_pures.
  + by wp_apply (twp_hl_frac_atom (PreTerm.PT2 O2Pair t1 t2)).
  + by wp_apply (twp_hl_frac_atom (PreTerm.PT2 O2Seal t1 t2)).
  + by wp_apply IH2; wp_pures; wp_apply IH1; wp_apply twp_add_frac.
  + by wp_apply IH2; wp_pures; wp_apply IH1; wp_apply twp_mul_frac.
  + by wp_apply (twp_hl_frac_atom (PreTerm.PT2 O2GMul t1 t2)).
  + by wp_apply (twp_hl_frac_atom (PreTerm.PT2 O2Exp t1 t2)).
Qed.

Lemma twp_hl_dh_add (m1 m2 : PreTerm.dhmap) E Ψ :
  Ψ (repr (PreTerm.dh_add m1 m2)) ⊢
  WP hl_dh_add (repr m1) (repr m2) @ E [{ Ψ }].
Proof.
rewrite /PreTerm.dh_add repr_fmapE FMap.to_list_cast -repr_fmapE.
iIntros "HΨ"; wp_lam; wp_pures;
  rewrite -(repr_frac_zero (T := PreTerm.pre_term)).
wp_apply (twp_fmap_merge eq_term leq_term twp_eq_pre_term twp_leq_pre_term
            Frac.zero Frac.zero eq_frac twp_eq_frac Frac.add); last done.
move=> a b E' Φ; iIntros "HΦ"; by wp_apply twp_add_frac.
Qed.

Lemma twp_hl_dh_opp (m : PreTerm.dhmap) E Ψ :
  Ψ (repr (PreTerm.dh_opp m)) ⊢ WP hl_dh_opp (repr m) @ E [{ Ψ }].
Proof.
rewrite /PreTerm.dh_opp repr_fmapE FMap.to_list_cast -repr_fmapE.
iIntros "HΨ"; wp_lam; rewrite -(repr_frac_zero (T := PreTerm.pre_term)).
wp_apply (twp_fmap_map Frac.zero eq_frac twp_eq_frac Frac.opp); last done.
move=> a E' Φ; iIntros "HΦ"; by wp_apply twp_frac_opp.
Qed.

Lemma twp_hl_dh_scale (r : Frac.frac PreTerm.pre_term) (m : PreTerm.dhmap)
    E Ψ :
  Ψ (repr (PreTerm.dh_scale r m)) ⊢
  WP hl_dh_scale (repr r) (repr m) @ E [{ Ψ }].
Proof.
rewrite /PreTerm.dh_scale repr_fmapE FMap.to_list_cast -repr_fmapE.
iIntros "HΨ"; wp_lam; wp_pures;
  rewrite -(repr_frac_zero (T := PreTerm.pre_term)).
wp_apply (twp_fmap_map Frac.zero eq_frac twp_eq_frac
            (λ f, Frac.mul f r)); last done.
move=> a E' Φ; iIntros "HΦ"; wp_pures; by wp_apply twp_mul_frac.
Qed.

Lemma twp_hl_dh_atom pt E Ψ :
  Ψ (repr ({[pt := Frac.one]} : PreTerm.dhmap)) ⊢
  WP fmap_singleton eq_frac frac_zero (repr pt) frac_one @ E [{ Ψ }].
Proof.
rewrite -(repr_frac_zero (T := PreTerm.pre_term))
  -(repr_frac_one (T := PreTerm.pre_term)).
exact: (twp_fmap_singleton Frac.zero eq_frac twp_eq_frac).
Qed.

Lemma twp_hl_dh_map pt E Ψ :
  Ψ (repr (PreTerm.dh_map pt)) ⊢ WP hl_dh_map (repr pt) @ E [{ Ψ }].
Proof.
elim: pt E Ψ => [o|o t IH|o t1 IH1 t2 IH2] E Ψ; iIntros "HΨ"; wp_rec.
- case: o => [n|a| | |]; wp_pures.
  + by wp_apply (twp_hl_dh_atom (PreTerm.PT0 (O0Int n))).
  + by wp_apply (twp_hl_dh_atom (PreTerm.PT0 (O0Nonce a))).
  + by wp_apply (twp_hl_dh_atom (PreTerm.PT0 O0Zero)).
  + by wp_apply (twp_hl_dh_atom (PreTerm.PT0 O0One)).
  + by rewrite -(repr_fmap_empty (T := PreTerm.pre_term) Frac.zero);
      iApply "HΨ".
- case: o => [kt| | | |]; wp_pures.
  + by wp_apply (twp_hl_dh_atom (PreTerm.PT1 (O1Key kt) t)).
  + by wp_apply (twp_hl_dh_atom (PreTerm.PT1 O1Hash t)).
  + by wp_apply (twp_hl_dh_atom (PreTerm.PT1 O1Opp t)).
  + by wp_apply (twp_hl_dh_atom (PreTerm.PT1 O1Inv t)).
  + by wp_apply IH; wp_apply twp_hl_dh_opp.
- case: o; wp_pures.
  + by wp_apply (twp_hl_dh_atom (PreTerm.PT2 O2Pair t1 t2)).
  + by wp_apply (twp_hl_dh_atom (PreTerm.PT2 O2Seal t1 t2)).
  + by wp_apply (twp_hl_dh_atom (PreTerm.PT2 O2Add t1 t2)).
  + by wp_apply (twp_hl_dh_atom (PreTerm.PT2 O2Mul t1 t2)).
  + by wp_apply IH2; wp_pures; wp_apply IH1; wp_apply twp_hl_dh_add.
  + wp_apply IH1; wp_pures; wp_apply twp_hl_frac_of.
    by wp_apply twp_hl_dh_scale.
Qed.

(** *** Encodings *)

Lemma twp_hl_fold_tree_ne (op : PreTerm.pre_term → PreTerm.pre_term →
                                PreTerm.pre_term) (opv : val) pt
    (l : list PreTerm.pre_term) E Ψ :
  (∀ pt1 pt2 E Φ, Φ (repr (op pt1 pt2)) ⊢
     WP opv (repr pt1) (repr pt2) @ E [{ Φ }]) →
  Ψ (repr (PreTerm.fold_tree_ne op pt l)) ⊢
  WP hl_fold_tree_ne opv (repr pt) (repr l) @ E [{ Ψ }].
Proof.
move=> opP; elim: l pt E Ψ => [|u l IH] pt E Ψ; rewrite repr_listE;
  iIntros "HΨ"; wp_rec; wp_pures; first by iApply "HΨ".
by wp_apply IH; wp_apply opP.
Qed.

Lemma twp_hl_fold_tree (op : PreTerm.pre_term → PreTerm.pre_term →
                             PreTerm.pre_term) (opv : val) u
    (l : list PreTerm.pre_term) E Ψ :
  (∀ pt1 pt2 E Φ, Φ (repr (op pt1 pt2)) ⊢
     WP opv (repr pt1) (repr pt2) @ E [{ Φ }]) →
  Ψ (repr (PreTerm.fold_tree op u l)) ⊢
  WP hl_fold_tree opv (repr u) (repr l) @ E [{ Ψ }].
Proof.
move=> opP; case: l => [|t l]; rewrite repr_listE; iIntros "HΨ"; wp_lam;
  wp_pures; first by iApply "HΨ".
by wp_apply twp_hl_fold_tree_ne.
Qed.

Lemma hl_oneE : hl_one = repr PreTerm.one.
Proof. by []. Qed.

Lemma hl_zeroE : hl_zero = repr (PreTerm.PT0 O0Zero).
Proof. by []. Qed.

Lemma hl_goneE : hl_gone = repr (PreTerm.PT0 O0GOne).
Proof. by []. Qed.

Lemma twp_hl_encode_mono (M : MSet.mset PreTerm.pre_term) E Ψ :
  Ψ (repr (PreTerm.encode_mono M)) ⊢ WP hl_encode_mono (repr M) @ E [{ Ψ }].
Proof.
rewrite repr_msetE; iIntros "HΨ"; wp_lam.
wp_apply (twp_hl_fold_tree (PreTerm.PT2 O2Mul) _ PreTerm.one);
  last by iApply "HΨ".
move=> *; exact: twp_hl_mk2.
Qed.

Lemma twp_hl_encode_sum (Ms : list (MSet.mset PreTerm.pre_term)) E Ψ :
  Ψ (repr (PreTerm.encode_sum Ms)) ⊢ WP hl_encode_sum (repr Ms) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam.
wp_apply (twp_map_list PreTerm.encode_mono hl_encode_mono Ms with "[//]").
  apply/Forall_forall => M _; iIntros (Φ) "_ HΦ".
  by wp_apply twp_hl_encode_mono; iApply "HΦ".
iIntros "_".
wp_apply (twp_hl_fold_tree (PreTerm.PT2 O2Add) _ (PreTerm.PT0 O0Zero)).
  move=> *; exact: twp_hl_mk2.
by iApply "HΨ".
Qed.

Lemma twp_hl_is_nil {A} `{!Repr A} (l : list A) E Ψ :
  Ψ #(bool_decide (l = @nil A)) ⊢ WP hl_is_nil (repr l) @ E [{ Ψ }].
Proof.
case: l => [|x l]; rewrite repr_listE; iIntros "HΨ"; wp_lam; wp_pures.
  by rewrite bool_decide_eq_true_2.
by rewrite bool_decide_eq_false_2.
Qed.

Lemma twp_hl_encode_poly (p : Poly.poly PreTerm.pre_term) E Ψ :
  Ψ (repr (PreTerm.encode_poly p)) ⊢ WP hl_encode_poly (repr p) @ E [{ Ψ }].
Proof.
rewrite repr_polyE repr_smsE repr_pair !repr_msetE /PreTerm.encode_poly.
rewrite /PreTerm.encode_signed.
move: (elements (SMS.pos _)) (elements (SMS.neg _)) => P N.
iIntros "HΨ"; wp_lam; wp_pures; wp_apply twp_hl_is_nil.
case: N => [|n N].
  by rewrite bool_decide_eq_true_2 //; wp_pures; wp_apply twp_hl_encode_sum.
rewrite bool_decide_eq_false_2 //; wp_pures; wp_apply twp_hl_is_nil.
case: P => [|m P].
  rewrite bool_decide_eq_true_2 //; wp_pures.
  by wp_apply (twp_hl_encode_sum (n :: N)); wp_apply twp_hl_mk1.
rewrite bool_decide_eq_false_2 //; wp_pures.
wp_apply (twp_hl_encode_sum (n :: N)); wp_apply twp_hl_mk1; wp_pures.
wp_apply (twp_hl_encode_sum (m :: P)).
by wp_apply (twp_hl_mk2 _ _ (PreTerm.PT1 O1Opp (PreTerm.encode_sum (n :: N)))).
Qed.

Lemma twp_hl_mod_of_frac (r : Frac.frac PreTerm.pre_term) E Ψ :
  Ψ (repr (PreTerm.mod_of_frac r)) ⊢ WP hl_mod_of_frac (repr r) @ E [{ Ψ }].
Proof.
rewrite repr_fracE repr_pair /PreTerm.mod_of_frac.
iIntros "HΨ"; wp_lam; wp_pures.
rewrite -(repr_poly_one (T := PreTerm.pre_term)).
wp_apply (twp_poly_eq eq_term twp_eq_pre_term).
case: bool_decide; wp_pures; first by wp_apply twp_hl_encode_poly.
wp_apply twp_hl_encode_poly; wp_apply twp_hl_mk1; wp_pures.
wp_apply (twp_hl_encode_poly (Frac.num r)).
by wp_apply (twp_hl_mk2 _ _
  (PreTerm.PT1 O1Inv (PreTerm.encode_poly (Frac.den r)))).
Qed.

Lemma twp_hl_mk_exp b (r : Frac.frac PreTerm.pre_term) E Ψ :
  Ψ (repr (PreTerm.mk_exp b r)) ⊢ WP hl_mk_exp (repr b) (repr r) @ E [{ Ψ }].
Proof.
rewrite /PreTerm.mk_exp; iIntros "HΨ"; wp_lam; wp_pures.
wp_apply twp_is_one_frac; case: bool_decide; wp_pures.
  by iApply "HΨ".
by wp_apply (twp_hl_mod_of_frac r); wp_apply (twp_hl_mk2 _ b).
Qed.

Lemma twp_hl_dh_of (m : PreTerm.dhmap) E Ψ :
  Ψ (repr (PreTerm.dh_of m)) ⊢ WP hl_dh_of (repr m) @ E [{ Ψ }].
Proof.
rewrite repr_fmapE; iIntros "HΨ"; wp_lam; wp_pures.
wp_apply (twp_map_list (λ e, PreTerm.mk_exp e.1 e.2) _ (FMap.to_list m)
            with "[//]").
  apply/Forall_forall => - [b r] _; iIntros (Φ) "_ HΦ"; wp_pures.
  by wp_apply twp_hl_mk_exp; iApply "HΦ".
iIntros "_".
wp_apply (twp_hl_fold_tree (PreTerm.PT2 O2GMul) _ (PreTerm.PT0 O0GOne)).
  move=> *; exact: twp_hl_mk2.
by iApply "HΨ".
Qed.

(** *** Operations *)

Lemma twp_hl_mul pt1 pt2 E Ψ :
  Ψ (repr (PreTerm.mul {[+ pt1; pt2 +]})) ⊢
  WP hl_mul (repr pt1) (repr pt2) @ E [{ Ψ }].
Proof.
rewrite /PreTerm.mul Frac.sprod_pair.
iIntros "HΨ"; wp_lam; wp_pures.
wp_apply twp_hl_frac_of; wp_apply twp_hl_frac_of.
by wp_apply twp_mul_frac; wp_apply twp_hl_mod_of_frac.
Qed.

Lemma twp_hl_inv pt E Ψ :
  Ψ (repr (PreTerm.mul (SMS.inv {[+ pt +]}))) ⊢
  WP hl_inv (repr pt) @ E [{ Ψ }].
Proof.
rewrite /PreTerm.mul Frac.sprod_inv Frac.sprod_singleton.
iIntros "HΨ"; wp_lam; wp_apply twp_hl_frac_of.
by wp_apply twp_inv_frac; wp_apply twp_hl_mod_of_frac.
Qed.

Lemma twp_hl_sum pt1 pt2 E Ψ :
  Ψ (repr (PreTerm.sum {[+ pt1; pt2 +]})) ⊢
  WP hl_sum (repr pt1) (repr pt2) @ E [{ Ψ }].
Proof.
rewrite /PreTerm.sum Frac.ssum_disj_union !Frac.ssum_singleton.
iIntros "HΨ"; wp_lam; wp_pures.
wp_apply twp_hl_frac_of; wp_apply twp_hl_frac_of.
by wp_apply twp_add_frac; wp_apply twp_hl_mod_of_frac.
Qed.

Lemma twp_hl_opp pt E Ψ :
  Ψ (repr (PreTerm.sum (SMS.inv {[+ pt +]}))) ⊢
  WP hl_opp (repr pt) @ E [{ Ψ }].
Proof.
rewrite /PreTerm.sum Frac.ssum_inv Frac.ssum_singleton.
iIntros "HΨ"; wp_lam; wp_apply twp_hl_frac_of.
by wp_apply twp_frac_opp; wp_apply twp_hl_mod_of_frac.
Qed.

Lemma twp_hl_gmul pt1 pt2 E Ψ :
  Ψ (repr (PreTerm.gmul {[+ pt1; pt2 +]})) ⊢
  WP hl_gmul (repr pt1) (repr pt2) @ E [{ Ψ }].
Proof.
rewrite /PreTerm.gmul PreTerm.dh_sum_pair.
iIntros "HΨ"; wp_lam; wp_pures.
wp_apply twp_hl_dh_map; wp_apply twp_hl_dh_map.
by wp_apply twp_hl_dh_add; wp_apply twp_hl_dh_of.
Qed.

Lemma twp_hl_ginv pt E Ψ :
  Ψ (repr (PreTerm.gmul (SMS.inv {[+ pt +]}))) ⊢
  WP hl_ginv (repr pt) @ E [{ Ψ }].
Proof.
rewrite /PreTerm.gmul PreTerm.dh_sum_inv_singleton.
iIntros "HΨ"; wp_lam; wp_apply twp_hl_dh_map.
by wp_apply twp_hl_dh_opp; wp_apply twp_hl_dh_of.
Qed.

Lemma twp_hl_exp b e E Ψ :
  Ψ (repr (PreTerm.exp b e)) ⊢ WP hl_exp (repr b) (repr e) @ E [{ Ψ }].
Proof.
rewrite /PreTerm.exp /PreTerm.exp_frac.
iIntros "HΨ"; wp_lam; wp_pures.
wp_apply twp_hl_dh_map; wp_apply twp_hl_frac_of.
by wp_apply twp_hl_dh_scale; wp_apply twp_hl_dh_of.
Qed.

End Proofs.
