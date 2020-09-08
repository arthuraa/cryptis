From mathcomp Require Import ssreflect.
From iris.heap_lang Require Import notation.
From iris.heap_lang Require Import primitive_laws.
From crypto Require Import lib basic symbols.

Inductive key_type := KSym | KAEnc | KADec.

Definition int_of_key_type kt : Z :=
  match kt with
  | KSym => 0
  | KAEnc => 1
  | KADec => 2
  end.

Definition key_type_of_int (n : Z) :=
  match n with
  | 0%Z => KSym
  | 1%Z => KAEnc
  | _ => KADec
  end.

Canonical key_typeO := leibnizO key_type.

Instance key_type_eq_dec : EqDecision key_type.
Proof.
refine (
  fun kt1 kt2 =>
    match kt1, kt2 with
    | KSym, KSym => left _
    | KAEnc, KAEnc => left _
    | KADec, KADec => left _
    | _, _ => right _
    end); congruence.
Defined.

Instance int_of_key_typeK : Cancel (=) key_type_of_int int_of_key_type.
Proof. by case. Qed.

Instance int_of_key_type_inj : Inj (=) (=) int_of_key_type.
Proof. by apply (@cancel_inj _ _ _ key_type_of_int); apply _. Qed.

Instance int_of_key_type_countable : Countable key_type.
Proof. apply (inj_countable' _ _ int_of_key_typeK). Qed.

Inductive term  :=
| TInt of Z
| TPair of term & term
| TNonce of loc
| TKey of key_type & loc
| TEnc of bool & loc & term.

Canonical termO := leibnizO term.

Notation TInt_tag := 0%Z.
Notation TPair_tag := 1%Z.
Notation TNonce_tag := 2%Z.
Notation TKey_tag := 3%Z.
Notation TEnc_tag := 4%Z.

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
    | TKey kt1 l1, TKey kt2 l2 =>
      cast_if_and (decide (kt1 = kt2)) (decide (l1 = l2))
    | TEnc asym1 l1 t1, TEnc asym2 l2 t2 =>
      cast_if_and3 (decide (asym1 = asym2)) (decide (l1 = l2)) (decide (t1 = t2))
    | _, _ => right _
    end); clear go; abstract intuition congruence.
Defined.

Fixpoint val_of_term_rec t : val :=
  match t with
  | TInt n => (#TInt_tag, #n)
  | TPair t1 t2 => (#TPair_tag, (val_of_term_rec t1, val_of_term_rec t2))%V
  | TNonce l => (#TNonce_tag, #l)%V
  | TKey kt l => (#TKey_tag, (#(int_of_key_type kt), #l))%V
  | TEnc b l t => (#TEnc_tag, (#b, #l, val_of_term_rec t))%V
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
  | PairV #(LitInt TKey_tag) (#(LitInt n), #(LitLoc l)) =>
    TKey (key_type_of_int n) l
  | PairV #(LitInt TEnc_tag) (#(LitBool b), #(LitLoc l), v) =>
    TEnc b l (term_of_val v)
  | _ => TInt 0
  end.

Global Instance val_of_termK : Cancel (=) term_of_val val_of_term.
Proof.
rewrite val_of_termE; elim=> //= *; try by congruence.
by rewrite cancel.
Qed.

Global Instance val_of_term_inj : Inj (=) (=) val_of_term.
Proof.
by apply (@cancel_inj _ _ _ term_of_val); apply _.
Qed.

Global Instance countable_term : Countable term.
Proof. apply (inj_countable' _ _ val_of_termK). Qed.
