(** Pre-terms

    A pre-term is a syntax tree with one constructor per arity: every
    operation, free or algebraic, is a tag of [term_op0], [term_op1] or
    [term_op2].  Normal forms are computed outside the type ([normalize.v]),
    so [deriving] provides equality, choice, countability and the order. *)

From cryptis Require Export mathcomp_compat.
From HB Require Import structures.
From mathcomp Require Import order boot.
From deriving Require Import deriving.
From Stdlib Require Import ZArith.ZArith Lia Utf8.
From iris.heap_lang Require locations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.POrderTheory Order.TotalTheory.

(* A nonce is a nominal wrapper around a heap location. *)
Record nonce := Nonce { nonce_loc : locations.loc }.

#[warnings="-projection-no-head-constant"]
HB.instance Definition _ := [isNew for nonce_loc].
HB.instance Definition _ := [Equality of nonce by <:].
HB.instance Definition _ := [Choice of nonce by <:].
HB.instance Definition _ := [Countable of nonce by <:].
HB.instance Definition _ := [Order of nonce by <:].

Inductive term_op0 :=
| O0Int of Z
| O0Nonce of nonce
| O0Zero
| O0One
| O0GOne.

Abbreviation TInt_tag := 0%Z.
Abbreviation TNonce_tag := 1%Z.
Abbreviation TZero_tag := 2%Z.
Abbreviation TOne_tag := 3%Z.
Abbreviation TGOne_tag := 4%Z.

Canonical term_op0_indDef := [indDef for term_op0_rect].
Canonical term_op0_indType := IndType term_op0 term_op0_indDef.
Definition term_op0_hasDecEq := [derive hasDecEq for term_op0].
#[warnings="-projection-no-head-constant"]
HB.instance Definition _ := term_op0_hasDecEq.
Definition term_op0_hasChoice := [derive hasChoice for term_op0].
#[warnings="-projection-no-head-constant"]
HB.instance Definition _ := term_op0_hasChoice.
Definition term_op0_isCountable := [derive isCountable for term_op0].
#[warnings="-projection-no-head-constant"]
HB.instance Definition _ := term_op0_isCountable.
Definition term_op0_isOrder := [derive isOrder for term_op0].
HB.instance Definition _ := term_op0_isOrder.

Inductive key_type := AEnc | ADec | Sign | Verify | SEnc.

Canonical key_type_indDef := [indDef for key_type_rect].
Canonical key_type_indType := IndType key_type key_type_indDef.
Definition key_type_hasDecEq := [derive hasDecEq for key_type].
#[warnings="-projection-no-head-constant"]
HB.instance Definition _ := key_type_hasDecEq.
Definition key_type_hasChoice := [derive hasChoice for key_type].
#[warnings="-projection-no-head-constant"]
HB.instance Definition _ := key_type_hasChoice.
Definition key_type_isCountable := [derive isCountable for key_type].
#[warnings="-projection-no-head-constant"]
HB.instance Definition _ := key_type_isCountable.
Definition key_type_isOrder := [derive isOrder for key_type].
HB.instance Definition _ := key_type_isOrder.

Inductive term_op1 :=
| O1Key of key_type
| O1Hash
| O1Opp
| O1Inv
| O1GInv.

Abbreviation TKey_tag := 0%Z.
Abbreviation THash_tag := 1%Z.
Abbreviation TOpp_tag := 2%Z.
Abbreviation TInv_tag := 3%Z.
Abbreviation TGInv_tag := 4%Z.

Canonical term_op1_indDef := [indDef for term_op1_rect].
Canonical term_op1_indType := IndType term_op1 term_op1_indDef.
Definition term_op1_hasDecEq := [derive hasDecEq for term_op1].
#[warnings="-projection-no-head-constant"]
HB.instance Definition _ := term_op1_hasDecEq.
Definition term_op1_hasChoice := [derive hasChoice for term_op1].
#[warnings="-projection-no-head-constant"]
HB.instance Definition _ := term_op1_hasChoice.
Definition term_op1_isCountable := [derive isCountable for term_op1].
#[warnings="-projection-no-head-constant"]
HB.instance Definition _ := term_op1_isCountable.
Definition term_op1_isOrder := [derive isOrder for term_op1].
HB.instance Definition _ := term_op1_isOrder.

Inductive term_op2 :=
| O2Pair
| O2Seal
| O2Add
| O2Mul
| O2GMul
| O2Exp.

Abbreviation TPair_tag := 0%Z.
Abbreviation TSeal_tag := 1%Z.
Abbreviation TAdd_tag := 2%Z.
Abbreviation TMul_tag := 3%Z.
Abbreviation TGMul_tag := 4%Z.
Abbreviation TExp_tag := 5%Z.

Canonical term_op2_indDef := [indDef for term_op2_rect].
Canonical term_op2_indType := IndType term_op2 term_op2_indDef.
Definition term_op2_hasDecEq := [derive hasDecEq for term_op2].
#[warnings="-projection-no-head-constant"]
HB.instance Definition _ := term_op2_hasDecEq.
Definition term_op2_hasChoice := [derive hasChoice for term_op2].
#[warnings="-projection-no-head-constant"]
HB.instance Definition _ := term_op2_hasChoice.
Definition term_op2_isCountable := [derive isCountable for term_op2].
#[warnings="-projection-no-head-constant"]
HB.instance Definition _ := term_op2_isCountable.
Definition term_op2_isOrder := [derive isOrder for term_op2].
HB.instance Definition _ := term_op2_isOrder.

Abbreviation TOp0_tag := 0%Z.
Abbreviation TOp1_tag := 1%Z.
Abbreviation TOp2_tag := 2%Z.

Module PreTerm.

Inductive pre_term :=
| PT0 of term_op0
| PT1 of term_op1 & pre_term
| PT2 of term_op2 & pre_term & pre_term.

Canonical pre_term_indDef := [indDef for pre_term_rect].
Canonical pre_term_indType := IndType pre_term pre_term_indDef.
Definition pre_term_hasDecEq := [derive hasDecEq for pre_term].
#[export, warnings="-projection-no-head-constant"]
HB.instance Definition _ := pre_term_hasDecEq.
Definition pre_term_hasChoice := [derive hasChoice for pre_term].
#[export, warnings="-projection-no-head-constant"]
HB.instance Definition _ := pre_term_hasChoice.
Definition pre_term_isCountable := [derive isCountable for pre_term].
#[export, warnings="-projection-no-head-constant"]
HB.instance Definition _ := pre_term_isCountable.
Definition pre_term_isOrder := [derive isOrder for pre_term].
#[export] HB.instance Definition _ := pre_term_isOrder.

Definition cons_num pt : Z :=
  match pt with
  | PT0 _ => TOp0_tag
  | PT1 _ _ => TOp1_tag
  | PT2 _ _ _ => TOp2_tag
  end.

#[local] Lemma le_alt d (T : orderType d) (x y : T) :
  (x <= y)%O = if x == y then true else (x <= y)%O.
Proof. by case: (ltgtP x y). Qed.

(** The derived order compares constructors first and then the arguments
    from left to right. *)
Lemma leqE pt1 pt2 :
  (pt1 <= pt2)%O =
  if cons_num pt1 == cons_num pt2 then
    match pt1, pt2 with
    | PT0 o1, PT0 o2 => (o1 <= o2)%O
    | PT1 o1 t1, PT1 o2 t2 =>
      if o1 == o2 then (t1 <= t2)%O else (o1 <= o2)%O
    | PT2 o1 t11 t12, PT2 o2 t21 t22 =>
      if o1 == o2 then
        if t11 == t21 then (t12 <= t22)%O else (t11 <= t21)%O
      else (o1 <= o2)%O
    | _, _ => false
    end
  else (cons_num pt1 <=? cons_num pt2)%Z.
Proof.
case: pt1 pt2 => [o1|o1 t1|o1 t11 t12] [o2|o2 t2|o2 t21 t22] //=.
- by rewrite [RHS]le_alt.
- by rewrite [(t1 <= t2)%O]le_alt.
- by rewrite (le_alt t12).
Qed.

Module Exports.
#[warnings="-projection-no-head-constant"]
HB.reexport.
End Exports.

End PreTerm.

Export PreTerm.Exports.
