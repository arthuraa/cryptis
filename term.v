From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
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

Instance repr_key_type : Repr key_type := λ kt, #(int_of_key_type kt).

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
Global Instance repr_term : Repr term := val_of_term.

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

Fixpoint symbols_of_term t : gset loc :=
  match t with
  | TInt _ => ∅
  | TPair t1 t2 => symbols_of_term t1 ∪ symbols_of_term t2
  | TNonce l => {[l]}
  | TKey _ l => {[l]}
  | TEnc _ l t => {[l]} ∪ symbols_of_term t
  end.

Module Spec.

Definition tag_def (n : nat) (t : term) := TPair (TInt n) t.
Definition tag_aux : seal tag_def. by eexists. Qed.
Definition tag := unseal tag_aux.
Lemma tag_eq : tag = tag_def. Proof. exact: seal_eq. Qed.

Definition untag_def (n : nat) (t : term) :=
  match t with
  | TPair (TInt m) t =>
    if decide (Z.of_nat n = m) then Some t else None
  | _ => None
  end.
Definition untag_aux : seal untag_def. by eexists. Qed.
Definition untag := unseal untag_aux.
Lemma untag_eq : untag = untag_def. Proof. exact: seal_eq. Qed.

Lemma tagK n t : untag n (tag n t) = Some t.
Proof.
rewrite untag_eq tag_eq /untag_def /tag_def /=.
by rewrite decide_left.
Qed.

Instance tag_inj : Inj2 (=) (=) (=) tag.
Proof.
rewrite tag_eq /tag_def => n1 t1 n2 t2 [] e ->.
split=> //; by apply (inj Z.of_nat).
Qed.

Definition as_int t :=
  if t is TInt n then Some n else None.

Definition untuple t :=
  match t with
  | TPair t1 t2 => Some (t1, t2)
  | _ => None
  end.

Fixpoint proj t n {struct t} :=
  match t, n with
  | TPair t _, 0 => Some t
  | TPair _ t, S n => proj t n
  | _, _ => None
  end.

Definition enc k t : option term :=
  match k with
  | TKey KSym l => Some (TEnc false l t)
  | TKey KAEnc l => Some (TEnc true l t)
  | _ => None
  end.

Definition dec k t : option term :=
  match k, t with
  | TKey KSym  l1, TEnc false l2 t
  | TKey KADec l1, TEnc true  l2 t =>
    if decide (l1 = l2) then Some t else None
  | _, _ => None
  end.

Definition is_key t :=
  match t with
  | TKey kt _ => Some kt
  | _ => None
  end.

Definition of_list_aux : seal (foldr TPair (TInt 0)). by eexists. Qed.
Definition of_list := unseal of_list_aux.
Lemma of_list_eq : of_list = foldr TPair (TInt 0).
Proof. exact: seal_eq. Qed.

Fixpoint to_list t : option (list term) :=
  match t with
  | TInt 0 => Some []
  | TPair t1 t2 =>
    match to_list t2 with
    | Some l => Some (t1 :: l)
    | None => None
    end
  | _ => None
  end.

Lemma of_listK l : to_list (of_list l) = Some l.
Proof. rewrite of_list_eq; by elim: l => //= t l ->. Qed.

End Spec.

Arguments repr_term /.
Arguments Spec.tag_def /.
Arguments Spec.untag_def /.
