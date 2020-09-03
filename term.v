From mathcomp Require Import ssreflect.
From iris.heap_lang Require Import notation.
From iris.heap_lang Require Import primitive_laws.
From crypto Require Import lib basic symbols.

Inductive term  :=
| TInt of Z
| TPair of term & term
| TNonce of loc
| TAKey of loc & bool
| TAEnc of loc & term
| TSKey of loc
| TSEnc of loc & term.

Canonical termO := leibnizO term.

Notation TInt_tag := 0%Z.
Notation TPair_tag := 1%Z.
Notation TNonce_tag := 2%Z.
Notation TAKey_tag := 3%Z.
Notation TAEnc_tag := 4%Z.
Notation TSKey_tag := 5%Z.
Notation TSEnc_tag := 6%Z.

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
    | TAKey l1 b1, TAKey l2 b2 =>
      cast_if_and (decide (l1 = l2)) (decide (b1 = b2))
    | TAEnc l1 t1, TAEnc l2 t2 =>
      cast_if_and (decide (l1 = l2)) (decide (t1 = t2))
    | TSKey l1, TSKey l2 =>
      cast_if (decide (l1 = l2))
    | TSEnc l1 t1, TSEnc l2 t2 =>
      cast_if_and (decide (l1 = l2)) (decide (t1 = t2))
    | _, _ => right _
    end); clear go; abstract intuition congruence.
Defined.

Fixpoint val_of_term_rec t : val :=
  match t with
  | TInt n => (#TInt_tag, #n)
  | TPair t1 t2 => (#TPair_tag, (val_of_term_rec t1, val_of_term_rec t2))%V
  | TNonce l => (#TNonce_tag, #l)%V
  | TAKey l b => (#TAKey_tag, (#l, #b))%V
  | TAEnc l t => (#TAEnc_tag, (#l, val_of_term_rec t))%V
  | TSKey l => (#TSKey_tag, #l)%V
  | TSEnc l t => (#TSEnc_tag, (#l, val_of_term_rec t))
  end.

Definition val_of_term := locked val_of_term_rec.
Lemma val_of_termE : val_of_term = val_of_term_rec.
Proof. by rewrite /val_of_term -lock. Qed.
Coercion val_of_term : term >-> val.
Instance as_val_term : AsVal term := val_of_term.

Fixpoint term_of_val v : term :=
  match v with
  | PairV (# (LitInt TInt_tag)) (# (LitInt n)) =>
    TInt n
  | PairV (# (LitInt TPair_tag)) (PairV v1 v2) =>
    TPair (term_of_val v1) (term_of_val v2)
  | PairV (# (LitInt TNonce_tag)) (# (LitLoc l)) =>
    TNonce l
  | PairV #(LitInt TAKey_tag) (PairV #(LitLoc l) #(LitBool b)) =>
    TAKey l b
  | PairV #(LitInt TAEnc_tag) (PairV #(LitLoc l) v) =>
    TAEnc l (term_of_val v)
  | PairV (# (LitInt TSKey_tag)) (# (LitLoc l)) =>
    TSKey l
  | PairV (# (LitInt TSEnc_tag)) (PairV (# (LitLoc l)) v) =>
    TSEnc l (term_of_val v)
  | _ => TInt 0
  end.

Global Instance val_of_termK : Cancel (=) term_of_val val_of_term.
Proof. rewrite val_of_termE; elim=> //= *; congruence. Qed.

Global Instance val_of_term_inj : Inj (=) (=) val_of_term.
Proof.
by apply (@cancel_inj _ _ _ term_of_val); apply _.
Qed.

Global Instance countable_term : Countable term.
Proof. apply (inj_countable' _ _ val_of_termK). Qed.
