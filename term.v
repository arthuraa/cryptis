From mathcomp Require Import ssreflect.
From mathcomp Require eqtype ssrbool path.
From deriving Require Import deriving.
From stdpp Require Import gmap.
From iris.heap_lang Require Import notation.
From iris.heap_lang Require Import primitive_laws.
From crypto Require Import mathcomp_compat lib basic symbols.
From crypto Require Export pre_term.

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

Canonical termO := leibnizO term.

Notation TInt_tag := 0%Z.
Notation TPair_tag := 1%Z.
Notation TNonce_tag := 2%Z.
Notation TKey_tag := 3%Z.
Notation TEnc_tag := 4%Z.
Notation THash_tag := 5%Z.
Notation TExp_tag := 6%Z.

Global Instance term_inhabited : Inhabited term.
Proof. exact: (populate (TInt 0)). Qed.

Global Instance term_eq_dec : EqDecision term := def_eq_decision _.

Section ValOfTerm.

Import PreTerm.

Fixpoint val_of_term_rec pt : val :=
  match pt with
  | PTInt n => (#TInt_tag, #n)
  | PTPair t1 t2 => (#TPair_tag, (val_of_term_rec t1, val_of_term_rec t2))%V
  | PTNonce l => (#TNonce_tag, #l)%V
  | PTKey kt t => (#TKey_tag, (#(int_of_key_type kt), val_of_term_rec t))%V
  | PTEnc t1 t2 => (#TEnc_tag, (val_of_term_rec t1, val_of_term_rec t2))%V
  | PTHash t => (#THash_tag, val_of_term_rec t)
  | PTExp t ts => (#TExp_tag, (val_of_term_rec t, repr (map val_of_term_rec ts)))
  end.

Fact val_of_term_key : unit. Proof. exact: tt. Qed.
Definition val_of_term :=
  locked_with val_of_term_key (
    fun t => val_of_term_rec (unfold_term t)
  ).
Lemma val_of_termE t :
  val_of_term t =
  match t with
  | TInt n => (#TInt_tag, #n)%V
  | TPair t1 t2 => (#TPair_tag, (val_of_term t1, val_of_term t2))%V
  | TNonce l => (#TNonce_tag, #l)%V
  | TKey kt t => (#TKey_tag, (#(int_of_key_type kt), val_of_term t))%V
  | TEnc t1 t2 => (#TEnc_tag, (val_of_term t1, val_of_term t2))%V
  | THash t => (#THash_tag, val_of_term t)%V
  | TExp' pt pts _ =>
    (#TExp_tag, (val_of_term_rec pt, repr (map val_of_term_rec pts)))%V
  end.
Proof.
rewrite /val_of_term locked_withE.
by case: t=> //=.
Qed.
Canonical val_of_term_unlock t := Unlockable (val_of_termE t).
Coercion val_of_term : term >-> val.
Global Instance repr_term : Repr term := val_of_term.

End ValOfTerm.

Lemma val_of_term_TExp t ts :
  ~ is_exp t ->
  path.sorted order.Order.le ts ->
  val_of_term (TExp t ts)
  = (#TExp_tag, (val_of_term t, repr (map val_of_term ts)))%V.
Proof.
move=> nexp sorted_ts.
rewrite /val_of_term locked_withE /= unfold_TExp.
rewrite PreTerm.exp_nexp //=; last by case: t nexp => //=.
rewrite order.Order.POrderTheory.sort_le_id // ?path.sorted_map.
  by rewrite map_map.
rewrite (_ : path.sorted _ _ = path.sorted order.Order.le ts) //.
by case: (path.sorted _ _) sorted_ts.
Qed.

Global Instance val_of_term_inj : Inj (=) (=) val_of_term.
Proof.
move=> t1 t2 e_t1t2; apply: unfold_term_inj.
move: e_t1t2; rewrite /val_of_term locked_withE.
move: {t1 t2} (unfold_term t1) (unfold_term t2).
elim.
- by move=> n1 [] //= n2 [] ->.
- by move=> t11 IH1 t12 IH2 [] //= t21 t22 [] /IH1 -> /IH2 ->.
- by move=> l1 [] //= l2 [] //= ->.
- by move=> kt1 t1 IH [] //= kt2 t2 [] /int_of_key_type_inj -> /IH ->.
- by move=> t11 IH1 t12 IH2 [] //= ?? [] /IH1 -> /IH2 ->.
- by move=> ? IH [] //= ? [] /IH ->.
- move=> t1 IHt ts1 IHts [] //= t2 ts2 [] /IHt -> e_ts; congr PreTerm.PTExp.
  move: e_ts; rewrite repr_list_eq.
  elim: ts1 IHts ts2 {t1 t2 IHt} => /= [_ [] //|t1 ts1 H [] IHt {}/H IHts].
  by case=> //= t2 ts2 [] /IHt -> /IHts ->.
Qed.

Global Instance countable_term : Countable term.
Proof. exact: def_countable. Qed.

Global Instance infinite_term : Infinite term.
Proof.
pose int_of_term (t : term) :=
  if t is TInt n then Some n else None.
apply (inj_infinite TInt int_of_term).
by move=> n; rewrite /int_of_term.
Qed.

Definition term_height t :=
  PreTerm.height (unfold_term t).

Fixpoint nonces_of_pre_term pt : gset loc :=
  match pt with
  | PreTerm.PTInt _ => ∅
  | PreTerm.PTPair t1 t2 => nonces_of_pre_term t1 ∪ nonces_of_pre_term t2
  | PreTerm.PTNonce l => {[l]}
  | PreTerm.PTKey _ t => nonces_of_pre_term t
  | PreTerm.PTEnc t1 t2 => nonces_of_pre_term t1 ∪ nonces_of_pre_term t2
  | PreTerm.PTHash t => nonces_of_pre_term t
  | PreTerm.PTExp t ts => nonces_of_pre_term t ∪ ⋃ map nonces_of_pre_term ts
  end.

Definition nonces_of_term_def (t : term) :=
  nonces_of_pre_term (unfold_term t).
Arguments nonces_of_term_def /.
Definition nonces_of_term_aux : seal nonces_of_term_def. by eexists. Qed.
Definition nonces_of_term := unseal nonces_of_term_aux.
Lemma nonces_of_term_eq : nonces_of_term = nonces_of_term_def.
Proof. exact: seal_eq. Qed.

Lemma nonces_of_termE t :
  nonces_of_term t =
  match t with
  | TInt _ => ∅
  | TPair t1 t2 => nonces_of_term t1 ∪ nonces_of_term t2
  | TNonce l => {[l]}
  | TKey _ t => nonces_of_term t
  | TEnc t1 t2 => nonces_of_term t1 ∪ nonces_of_term t2
  | THash t => nonces_of_term t
  | TExp' pt pts _ => nonces_of_pre_term pt ∪ ⋃ map nonces_of_pre_term pts
  end.
Proof.
by rewrite nonces_of_term_eq; case: t => //=.
Qed.

Lemma nonces_of_term_TExp t ts :
  nonces_of_term (TExp t ts)
  = nonces_of_term t ∪ ⋃ map nonces_of_term ts.
Proof.
rewrite nonces_of_term_eq /nonces_of_term_def unfold_TExp.
case: PreTerm.expP' => [pt' pts' pts'' -> e_pts''|pts' _ e_pts'] //=.
- by rewrite [in LHS]e_pts'' map_app union_list_app_L assoc_L map_map.
- by rewrite [in LHS]e_pts' map_map.
Qed.

Module Spec.

Implicit Types N : namespace.

Definition tag_def N (t : term) :=
  TPair (TInt (Zpos (encode N))) t.
Definition tag_aux : seal tag_def. by eexists. Qed.
Definition tag := unseal tag_aux.
Lemma tag_eq : tag = tag_def. Proof. exact: seal_eq. Qed.

Definition untag_def N (t : term) :=
  match t with
  | TPair (TInt (Zpos m)) t =>
    if decide (encode N = m) then Some t else None
  | _ => None
  end.
Definition untag_aux : seal untag_def. by eexists. Qed.
Definition untag := unseal untag_aux.
Lemma untag_eq : untag = untag_def. Proof. exact: seal_eq. Qed.

Lemma tagK N t : untag N (tag N t) = Some t.
Proof.
rewrite untag_eq tag_eq /untag_def /tag_def /=.
by rewrite decide_left.
Qed.

Instance tag_inj : Inj2 (=) (=) (=) tag.
Proof.
rewrite tag_eq /tag_def => c1 t1 c2 t2 [] e ->.
split=> //; by apply: inj e.
Qed.

Lemma untagK N t1 t2 :
  untag N t1 = Some t2 ->
  t1 = tag N t2.
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
rewrite of_list_eq /=; elim/term_ind': t ts => //.
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
