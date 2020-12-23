From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From iris.heap_lang Require Import notation.
From iris.heap_lang Require Import primitive_laws.
From crypto Require Import lib basic symbols.

Inductive key_type := Enc | Dec.

Definition int_of_key_type kt : Z :=
  match kt with
  | Enc => 0
  | Dec => 1
  end.

Definition key_type_of_int (n : Z) :=
  match n with
  | 0%Z => Enc
  | _   => Dec
  end.

Canonical key_typeO := leibnizO key_type.

Instance key_type_eq_dec : EqDecision key_type.
Proof.
refine (
  fun kt1 kt2 =>
    match kt1, kt2 with
    | Enc, Enc => left _
    | Dec, Dec => left _
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
| TKey of key_type & term
| TEnc of term & term.

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
    | TEnc t11 t12, TEnc t21 t22 =>
      cast_if_and (decide (t11 = t21)) (decide (t12 = t22))
    | _, _ => right _
    end); clear go; abstract intuition congruence.
Defined.

Fixpoint val_of_term_rec t : val :=
  match t with
  | TInt n => (#TInt_tag, #n)
  | TPair t1 t2 => (#TPair_tag, (val_of_term_rec t1, val_of_term_rec t2))%V
  | TNonce l => (#TNonce_tag, #l)%V
  | TKey kt t => (#TKey_tag, (#(int_of_key_type kt), val_of_term_rec t))%V
  | TEnc t1 t2 => (#TEnc_tag, (val_of_term_rec t1, val_of_term_rec t2))%V
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
  | PairV #(LitInt TKey_tag) (#(LitInt n), v) =>
    TKey (key_type_of_int n) (term_of_val v)
  | PairV #(LitInt TEnc_tag) (v1, v2) =>
    TEnc (term_of_val v1) (term_of_val v2)
  | _ => TInt 0
  end.

Global Instance val_of_termK : Cancel (=) term_of_val val_of_term.
Proof.
rewrite val_of_termE; elim=> //= *; try by congruence.
by rewrite cancel; congruence.
Qed.

Global Instance val_of_term_inj : Inj (=) (=) val_of_term.
Proof.
by apply (@cancel_inj _ _ _ term_of_val); apply _.
Qed.

Global Instance countable_term : Countable term.
Proof. apply (inj_countable' _ _ val_of_termK). Qed.

Definition int_of_term (t : term) :=
  match t with TInt n => Some n | _ => None end.

Global Instance infinite_term : Infinite term.
Proof. by apply (inj_infinite TInt int_of_term). Qed.

Fixpoint nonces_of_term t : gset loc :=
  match t with
  | TInt _ => ∅
  | TPair t1 t2 => nonces_of_term t1 ∪ nonces_of_term t2
  | TNonce l => {[l]}
  | TKey _ t => nonces_of_term t
  | TEnc t1 t2 => nonces_of_term t1 ∪ nonces_of_term t2
  end.

Module Spec.

Definition tag_def (c : string) (t : term) :=
  TPair (TInt (Zpos (encode c))) t.
Definition tag_aux : seal tag_def. by eexists. Qed.
Definition tag := unseal tag_aux.
Lemma tag_eq : tag = tag_def. Proof. exact: seal_eq. Qed.

Definition untag_def (c : string) (t : term) :=
  match t with
  | TPair (TInt (Zpos m)) t =>
    if decide (encode c = m) then Some t else None
  | _ => None
  end.
Definition untag_aux : seal untag_def. by eexists. Qed.
Definition untag := unseal untag_aux.
Lemma untag_eq : untag = untag_def. Proof. exact: seal_eq. Qed.

Lemma tagK c t : untag c (tag c t) = Some t.
Proof.
rewrite untag_eq tag_eq /untag_def /tag_def /=.
by rewrite decide_left.
Qed.

Instance tag_inj : Inj2 (=) (=) (=) tag.
Proof.
rewrite tag_eq /tag_def => c1 t1 c2 t2 [] e ->.
split=> //; by apply: inj e.
Qed.

Lemma untagK c t1 t2 :
  untag c t1 = Some t2 ->
  t1 = tag c t2.
Proof.
rewrite untag_eq tag_eq /=.
case: t1=> [] // [] // [] //= m.
by case: decide => // <- _ [->].
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
  | TKey Enc k => Some (TEnc k t)
  | _ => None
  end.

Definition dec k t : option term :=
  match k, t with
  | TKey Dec k1, TEnc k2 t =>
    if decide (k1 = k2) then Some t else None
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

Lemma to_listK t ts :
  to_list t = Some ts →
  t = of_list ts.
Proof.
rewrite of_list_eq /=; elim: t ts => //.
  by case=> [] // _ [<-].
move=> t _ ts' IH /= ts.
case e: to_list => [ts''|] // [<-].
by rewrite /= (IH _ e).
Qed.

Inductive to_list_spec : term → option (list term) → Type :=
| ToListSome ts : to_list_spec (of_list ts) (Some ts)
| ToListNone t  : to_list_spec t None.

Lemma to_listP t : to_list_spec t (to_list t).
Proof.
case e: to_list => [ts|]; last constructor.
by rewrite (to_listK _ _ e); constructor.
Qed.

Lemma of_list_inj : Inj eq eq of_list.
Proof.
move=> ts1 ts2 e; apply: Some_inj.
by rewrite -of_listK e of_listK.
Qed.

Definition tenc c k t := enc k (tag c t).

Definition tdec c k t :=
  match dec k t with
  | Some t => untag c t
  | None => None
  end.

End Spec.

Arguments repr_term /.
Arguments Spec.tag_def /.
Arguments Spec.untag_def /.

Existing Instance Spec.of_list_inj.
