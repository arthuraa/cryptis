From cryptis Require Import mathcomp_compat lib.
From cryptis.lib Require Import list_sort.
From mathcomp Require Import ssreflect.
From mathcomp Require Import order.
From mathcomp Require eqtype ssrbool path.
From deriving Require Import deriving.
From stdpp Require Import gmap sorting lexico.
From iris.heap_lang Require Import notation.
From iris.heap_lang Require Import primitive_laws.
From cryptis.core.pre_term Require Import base.

Canonical term_op0O := leibnizO term_op0.

#[global]
Instance term_op0_eq_dec : EqDecision term_op0.
Proof. exact: def_eq_decision. Defined.

#[global]
Instance repr_term_op0 : Repr term_op0 := λ o,
  match o with
  | O0Int n => (#TInt_tag, #n)%V
  | O0Nonce a => (#TNonce_tag, #(nonce_loc a))%V
  | O0Zero => (#TZero_tag, #())%V
  | O0One => (#TOne_tag, #())%V
  | O0GOne => (#TGOne_tag, #())%V
  end.

Definition int_of_key_type kt : Z :=
  match kt with
  | AEnc => 0
  | ADec => 1
  | Sign => 2
  | Verify => 3
  | SEnc => 4
  end.

Definition key_type_of_int (n : Z) :=
  match n with
  | 0%Z => AEnc
  | 1%Z => ADec
  | 2%Z => Sign
  | 3%Z => Verify
  | _ => SEnc
  end.

Canonical key_typeO := leibnizO key_type.

#[global]
Instance key_type_eq_dec : EqDecision key_type.
Proof. exact: def_eq_decision. Defined.

#[global]
Instance int_of_key_typeK : Cancel (=) key_type_of_int int_of_key_type.
Proof. by case. Qed.

#[global]
Instance int_of_key_type_inj : Inj (=) (=) int_of_key_type.
Proof. by apply (@cancel_inj _ _ _ key_type_of_int); apply _. Qed.

#[global]
Instance int_of_key_type_countable : Countable key_type.
Proof. apply (inj_countable' _ _ int_of_key_typeK). Qed.

#[global]
Instance repr_key_type : Repr key_type := λ kt, #(int_of_key_type kt).

Canonical term_op1O := leibnizO term_op1.

#[global]
Instance term_op1_eq_dec : EqDecision term_op1.
Proof. exact: def_eq_decision. Defined.

Instance repr_term_op1 : Repr term_op1 := λ o,
  match o with
  | O1Key kt => (#TKey_tag, repr kt)%V
  | O1Hash => (#THash_tag, #())%V
  | O1Opp => (#TOpp_tag, #())%V
  | O1Inv => (#TInv_tag, #())%V
  | O1GInv => (#TGInv_tag, #())%V
  end.

Canonical term_op2O := leibnizO term_op2.

#[global]
Instance term_op2_eq_dec : EqDecision term_op2.
Proof. exact: def_eq_decision. Defined.

Definition int_of_term_op2 (o : term_op2) : Z :=
  match o with
  | O2Pair => TPair_tag
  | O2Seal => TSeal_tag
  | O2Add => TAdd_tag
  | O2Mul => TMul_tag
  | O2GMul => TGMul_tag
  | O2Exp => TExp_tag
  end.

Instance repr_term_op2 : Repr term_op2 := λ o, #(int_of_term_op2 o).
Arguments repr_term_op2 /.

Section ValOfPreTerm.

Import PreTerm.

Definition val_of_pre_term : Repr pre_term := fix val_of_pre_term pt :=
  match pt with
  | PT0 o => (#TOp0_tag, repr o)%V
  | PT1 o t => (#TOp1_tag, (repr o, val_of_pre_term t))%V
  | PT2 o t1 t2 =>
    (#TOp2_tag, (repr o, val_of_pre_term t1, val_of_pre_term t2))%V
  end.

#[global] Existing Instance val_of_pre_term.

End ValOfPreTerm.

Definition nonce_eq_dec : EqDecision nonce := Eval hnf in def_eq_decision _.
#[global] Existing Instance nonce_eq_dec.
#[global] Instance nonce_countable : Countable nonce.
Proof. exact: def_countable. Qed.
#[global] Instance nonce_inhabited : Inhabited nonce :=
  populate (Nonce inhabitant).

Definition nonces_of_term_op0 o : gset nonce :=
  if o is O0Nonce a then {[a]} else ∅.

Fixpoint nonces_of_pre_term pt : gset nonce :=
  match pt with
  | PreTerm.PT0 o => nonces_of_term_op0 o
  | PreTerm.PT1 _ t => nonces_of_pre_term t
  | PreTerm.PT2 _ t1 t2 => nonces_of_pre_term t1 ∪ nonces_of_pre_term t2
  end.

#[global] Instance pre_term_inhabited : Inhabited PreTerm.pre_term.
Proof. exact: (populate (PreTerm.PT0 (O0Int 0))). Qed.

Definition pre_term_eq_dec : EqDecision PreTerm.pre_term :=
  Eval hnf in def_eq_decision _.
#[global] Existing Instance pre_term_eq_dec.

#[global] Instance pre_term_countable : Countable PreTerm.pre_term :=
  def_countable _ pre_term_eq_dec.

(** ** Order

    [lexico] is the strict part of the order derived in [base.v], and
    [pt_order] is the order itself. *)
Section PreTermOrder.
#[warnings="-ambiguous-paths"]
Import Order.POrderTheory Order.TotalTheory ssrbool boot.eqtype.
Open Scope order_scope.

(* [is_true] is spelled out so that the relations land on ssreflect's boolean
   coercion, which the mathcomp order lemmas expect, rather than stdpp's
   [Is_true]. *)
#[global] Instance pre_term_lexico : Lexico PreTerm.pre_term :=
  λ x y, is_true (x < y).

#[global] Instance pre_term_lexico_strict :
  StrictOrder (@lexico PreTerm.pre_term _).
Proof.
split; first by move=> x; rewrite /complement /lexico /pre_term_lexico ltxx.
move=> x y z; exact: lt_trans.
Qed.

#[global] Instance pre_term_lexico_trichotomyT :
  TrichotomyT (@lexico PreTerm.pre_term _).
Proof.
refine (λ x y,
  match Sumbool.sumbool_of_bool (x < y) with
  | left p => inleft (left p)
  | right p =>
      match Sumbool.sumbool_of_bool (y < x) with
      | left q => inright q
      | right q => inleft (right _)
      end
  end).
abstract (by apply/eqP; rewrite eq_le !leNgt p q).
Defined.

Definition pt_order : relation PreTerm.pre_term := λ x y, is_true (x <= y).

#[global] Instance pt_order_dec : RelDecision pt_order :=
  λ x y, bool_eq_dec (x <= y) true.

Lemma pt_order_lexico x y : pt_order x y ↔ x = y ∨ lexico x y.
Proof.
rewrite /pt_order /lexico /pre_term_lexico le_eqVlt.
split; first by case/orP => H; [left; apply/eqP|right].
by case=> [->|H]; apply/orP; [left|right].
Qed.

Lemma bool_decide_pt_order x y : bool_decide (pt_order x y) = (x <= y).
Proof. by apply/bool_decide_reflect/idP. Qed.

End PreTermOrder.

#[global] Instance repr_term_op0_inj : Inj (=) (=) (@repr term_op0 _).
Proof. by case=> [?|[?]| | |] [?|[?]| | |] //= [<-]. Qed.

#[global] Instance repr_term_op1_inj : Inj (=) (=) (@repr term_op1 _).
Proof. by case=> [?| | | |] [?| | | |] //= [/int_of_key_type_inj ->]. Qed.

#[global] Instance int_of_term_op2_inj : Inj (=) (=) int_of_term_op2.
Proof. by case=> [] []. Qed.

#[global] Instance repr_term_op2_inj : Inj (=) (=) (@repr term_op2 _).
Proof. by move=> o1 o2 [/int_of_term_op2_inj]. Qed.

#[global] Instance val_of_pre_term_inj : Inj (=) (=) val_of_pre_term.
Proof.
move=> t1; elim: t1 => [o1|o1 t1 IH|o1 t11 IH1 t12 IH2].
- by case=> //= o2 [] /repr_term_op0_inj ->.
- by case=> //= o2 t2 [] /repr_term_op1_inj -> /IH ->.
- by case=> //= o2 t21 t22 [] /int_of_term_op2_inj -> /IH1 -> /IH2 ->.
Qed.
