From mathcomp Require Import ssreflect.
From iris.heap_lang Require Import notation.
From iris.heap_lang Require Import primitive_laws.
From crypto Require Import lib basic symbols.

Inductive term  :=
| TInt of Z
| TPair of term & term
| TNonce of loc
| TSKey of loc
| TSEnc of loc & term.

Canonical termO := leibnizO term.

Global Instance term_eq_dec : EqDecision term.
Proof.
refine (
  fix go t1 t2 {struct t1} : Decision (t1 = t2) :=
    match t1, t2 with
    | TInt n1, TInt n2 =>
      cast_if (decide (n1 = n2))
    | TPair t11 t12, TPair t21 t22  =>
      cast_if_and (decide (t11 = t21)) (decide (t12 = t22))
    | TNonce l1, TNonce l2 =>
      cast_if (decide (l1 = l2))
    | TSKey l1, TSKey l2 =>
      cast_if (decide (l1 = l2))
    | TSEnc l1 t1, TSEnc l2 t2 =>
      cast_if_and (decide (l1 = l2)) (decide (t1 = t2))
    | _, _ => right _
    end); clear go; abstract intuition congruence.
Defined.

Fixpoint val_of_term t : val :=
  match t with
  | TInt n => (#0, #n)
  | TPair t1 t2 => (#1, (val_of_term t1, val_of_term t2))%V
  | TNonce l => (#2, #l)%V
  | TSKey l => (#3, #l)%V
  | TSEnc l t => (#4, (#l, val_of_term t))
  end.

Fixpoint term_of_val v : term :=
  match v with
  | PairV (# (LitInt 0)) (# (LitInt n)) =>
    TInt n
  | PairV (# (LitInt 1)) (PairV v1 v2) =>
    TPair (term_of_val v1) (term_of_val v2)
  | PairV (# (LitInt 2)) (# (LitLoc l)) =>
    TNonce l
  | PairV (# (LitInt 3)) (# (LitLoc l)) =>
    TSKey l
  | PairV (# (LitInt 4)) (PairV (# (LitLoc l)) v) =>
    TSEnc l (term_of_val v)
  | _ => TInt 0
  end.

Global Instance val_of_termK : Cancel (=) term_of_val val_of_term.
Proof. elim=> //= *; congruence. Qed.

Global Instance val_of_term_inj : Inj (=) (=) val_of_term.
Proof.
by apply (@cancel_inj _ _ _ term_of_val); apply _.
Qed.

Global Instance countable_term : Countable term.
Proof. apply (inj_countable' _ _ val_of_termK). Qed.
