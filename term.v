From mathcomp Require Import ssreflect.
From mathcomp Require eqtype ssrbool path.
From deriving Require Import deriving.
From stdpp Require Import gmap.
From iris.heap_lang Require Import notation.
From iris.heap_lang Require Import primitive_laws.
From cryptis Require Import mathcomp_compat lib.
From cryptis Require Export pre_term.

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

#[global]
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

Canonical termO := leibnizO term.

Global Instance TExp_proper : Proper ((=) ==> (≡ₚ) ==> (=)) TExp.
Proof.
by move=> t _ <- ts1 ts2 e; apply/TExp_inj; eauto.
Qed.

Lemma TExpC2 g t1 t2 : TExp g [t1; t2] = TExp g [t2; t1].
Proof.
suff -> : [t1; t2] ≡ₚ [t2; t1] by [].
exact/Permutation_swap.
Qed.

Global Instance pre_term_inhabited : Inhabited PreTerm.pre_term.
Proof. exact: (populate (PreTerm.PTInt 0)). Qed.

Definition pre_term_eq_dec : EqDecision PreTerm.pre_term :=
  Eval hnf in def_eq_decision _.
Global Existing Instance pre_term_eq_dec.

Global Instance term_inhabited : Inhabited term.
Proof. exact: (populate (TInt 0)). Qed.

Definition term_eq_dec : EqDecision term :=
  Eval hnf in def_eq_decision _.
Global Existing Instance term_eq_dec.

Inductive subterm (t : term) : term → Prop :=
| STRefl : subterm t t
| STPair1 t1 t2 of subterm t t1 : subterm t (TPair t1 t2)
| STPair2 t1 t2 of subterm t t2 : subterm t (TPair t1 t2)
| STKey kt t' of subterm t t' : subterm t (TKey kt t')
| STEnc1 k t' of subterm t k : subterm t (TEnc k t')
| STEnc2 k t' of subterm t t' : subterm t (TEnc k t')
| STHash t' of subterm t t' : subterm t (THash t')
| STExp1 t' ts of subterm t t' : subterm t (TExp t' ts)
| STExp2 t' t'' ts of subterm t t'' & t'' ∈ ts : subterm t (TExp t' ts).

Section ValOfTerm.

Import PreTerm.

Fixpoint val_of_pre_term_rec pt : val :=
  match pt with
  | PTInt n =>
    (#TInt_tag, #n)
  | PTPair t1 t2 =>
    (#TPair_tag, (val_of_pre_term_rec t1, val_of_pre_term_rec t2))%V
  | PTNonce l =>
    (#TNonce_tag, #l)%V
  | PTKey kt t =>
    (#TKey_tag, (#(int_of_key_type kt), val_of_pre_term_rec t))%V
  | PTEnc t1 t2 =>
    (#TEnc_tag, (val_of_pre_term_rec t1, val_of_pre_term_rec t2))%V
  | PTHash t =>
    (#THash_tag, val_of_pre_term_rec t)
  | PTExp t ts =>
    (#TExp_tag, (val_of_pre_term_rec t,
                 repr_list (map val_of_pre_term_rec ts)))
  end.

Definition val_of_pre_term_aux : seal val_of_pre_term_rec. by eexists. Qed.
Definition val_of_pre_term : Repr pre_term := unseal val_of_pre_term_aux.
Lemma val_of_pre_term_unseal : val_of_pre_term = val_of_pre_term_rec.
Proof. exact: seal_eq. Qed.
Global Existing Instance val_of_pre_term.

Fixpoint val_of_term_rec t : val :=
  match t with
  | TInt n =>
    (#TInt_tag, #n)
  | TPair t1 t2 =>
    (#TPair_tag, (val_of_term_rec t1, val_of_term_rec t2))%V
  | TNonce l =>
    (#TNonce_tag, #l)%V
  | TKey kt t =>
    (#TKey_tag, (#(int_of_key_type kt), val_of_term_rec t))%V
  | TEnc t1 t2 =>
    (#TEnc_tag, (val_of_term_rec t1, val_of_term_rec t2))%V
  | THash t =>
    (#THash_tag, val_of_term_rec t)
  | TExp' t ts _ =>
    (#TExp_tag, (val_of_term_rec t, repr ts))
  end.

Definition val_of_term_aux : seal val_of_term_rec. by eexists. Qed.
Definition val_of_term : term -> val := unseal val_of_term_aux.
Lemma val_of_term_unseal : val_of_term = val_of_term_rec.
Proof. exact: seal_eq. Qed.
Coercion val_of_term : term >-> val.
Global Instance repr_term : Repr term := val_of_term.

Lemma val_of_pre_term_unfold t :
  val_of_pre_term (unfold_term t) = val_of_term t.
Proof.
rewrite val_of_term_unseal val_of_pre_term_unseal.
elim/term_ind': t => //=; try by move=> *; congruence.
move=> t -> pts _.
by rewrite [repr_list pts]repr_list_val /repr val_of_pre_term_unseal.
Qed.

End ValOfTerm.

Lemma val_of_term_TExp t ts :
  ~ is_exp t ->
  path.sorted order.Order.le ts ->
  val_of_term (TExp t ts) = (#TExp_tag, (val_of_term t, repr ts))%V.
Proof.
move=> nexp sorted_ts.
rewrite -[LHS]val_of_pre_term_unfold unfold_TExp.
rewrite order.Order.POrderTheory.sort_le_id // ?path.sorted_map; last first.
  rewrite (_ : path.sorted _ _ = path.sorted order.Order.le ts) //.
  by case: (path.sorted _ _) sorted_ts.
rewrite -[in RHS](val_of_pre_term_unfold t) val_of_pre_term_unseal /=.
rewrite [repr_list ts]repr_list_val map_map.
do !congr PairV; congr repr_list.
elim: ts {sorted_ts} => //= {nexp}t ts -> /=.
by rewrite /repr_term -val_of_pre_term_unfold val_of_pre_term_unseal.
Qed.

Global Instance val_of_pre_term_inj : Inj (=) (=) val_of_pre_term.
Proof.
rewrite val_of_pre_term_unseal.
elim.
- by move=> n1 [] //= n2 [] ->.
- by move=> t11 IH1 t12 IH2 [] //= t21 t22 [] /IH1 -> /IH2 ->.
- by move=> l1 [] //= l2 [] //= ->.
- by move=> kt1 t1 IH [] //= kt2 t2 [] /int_of_key_type_inj -> /IH ->.
- by move=> t11 IH1 t12 IH2 [] //= ?? [] /IH1 -> /IH2 ->.
- by move=> ? IH [] //= ? [] /IH ->.
- move=> t1 IHt ts1 IHts [] //= t2 ts2 [] /IHt -> e_ts; congr PreTerm.PTExp.
  move: e_ts; rewrite repr_list_unseal.
  elim: ts1 IHts ts2 {t1 t2 IHt} => /= [_ [] //|t1 ts1 H [] IHt {}/H IHts].
  by case=> //= t2 ts2 [] /IHt -> /IHts ->.
Qed.

Global Instance val_of_term_inj : Inj (=) (=) val_of_term.
Proof.
move=> t1 t2 e_t1t2; apply: unfold_term_inj.
apply: val_of_pre_term_inj.
by rewrite !val_of_pre_term_unfold.
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
Lemma nonces_of_term_unseal : nonces_of_term = nonces_of_term_def.
Proof. exact: seal_eq. Qed.

Lemma nonces_of_termE' t :
  nonces_of_term t =
  match t with
  | TInt _ => ∅
  | TPair t1 t2 => nonces_of_term t1 ∪ nonces_of_term t2
  | TNonce l => {[l]}
  | TKey _ t => nonces_of_term t
  | TEnc t1 t2 => nonces_of_term t1 ∪ nonces_of_term t2
  | THash t => nonces_of_term t
  | TExp' t pts _ => nonces_of_term t ∪ ⋃ map nonces_of_pre_term pts
  end.
Proof.
by rewrite nonces_of_term_unseal; case: t => //=.
Qed.

Lemma nonces_of_term_TExp t ts :
  nonces_of_term (TExp t ts)
  = nonces_of_term t ∪ ⋃ map nonces_of_term ts.
Proof.
rewrite nonces_of_term_unseal /nonces_of_term_def.
case: unfold_TExpP => pts' e_pts' /=.
by rewrite [in LHS]e_pts' map_map.
Qed.

Definition nonces_of_termE := (nonces_of_term_TExp, nonces_of_termE').

Fixpoint subterms_pre_def t : gset term :=
  {[fold_term t]} ∪
  match t with
  | PreTerm.PTInt _ => ∅
  | PreTerm.PTPair t1 t2 => subterms_pre_def t1 ∪ subterms_pre_def t2
  | PreTerm.PTNonce _ => ∅
  | PreTerm.PTKey _ t => subterms_pre_def t
  | PreTerm.PTEnc t1 t2 => subterms_pre_def t1 ∪ subterms_pre_def t2
  | PreTerm.PTHash t => subterms_pre_def t
  | PreTerm.PTExp t ts => subterms_pre_def t ∪ ⋃ map subterms_pre_def ts
  end.

Definition subterms_def t :=
  subterms_pre_def (unfold_term t).
Arguments subterms_def /.
Definition subterms_aux : seal subterms_def. by eexists. Qed.
Definition subterms := unseal subterms_aux.
Lemma subterms_unseal : subterms = subterms_def.
Proof. exact: seal_eq. Qed.

Lemma subtermsE' t :
  subterms t =
  {[t]} ∪
  match t with
  | TInt _ => ∅
  | TPair t1 t2 => subterms t1 ∪ subterms t2
  | TNonce _ => ∅
  | TKey _ t => subterms t
  | TEnc t1 t2 => subterms t1 ∪ subterms t2
  | THash t => subterms t
  | TExp' t pts _ => subterms t ∪ ⋃ map subterms_pre_def pts
  end.
Proof.
rewrite subterms_unseal /=.
case: t =>> //=; try by rewrite fold_termE ?unfold_termK.
by rewrite fold_termE unfold_termK TExp'E.
Qed.

Lemma subterms_TExp t ts :
  subterms (TExp t ts) = {[TExp t ts]} ∪ (subterms t ∪ ⋃ (subterms <$> ts)).
Proof.
rewrite subtermsE'; congr (_ ∪ _).
case: TExpP => pts ? e_pts.
by rewrite [in LHS]e_pts map_map subterms_unseal.
Qed.

Definition subtermsE := (subterms_TExp, subtermsE').

Ltac solve_subtermsP :=
  intros;
  repeat match goal with
  | H : context[subterms (?X ?Y)] |- _ =>
      rewrite [subterms (X Y)]subtermsE /= in H
  | H : _ ∈ {[_]} |- _ =>
      rewrite elem_of_singleton in H;
      rewrite {}H
  | H : _ ∈ _ ∪ _ |- _ =>
      rewrite elem_of_union in H;
      destruct H
  | H : _ ∈ ∅ |- _ =>
      rewrite elem_of_empty in H;
      destruct H
  | H1 : ?P, H2 : ?P -> ?Q |- _ =>
      move/(_ H1) in H2
  end;
  eauto using subterm.

Lemma subtermsP t1 t2 : subterm t1 t2 ↔ t1 ∈ subterms t2.
Proof.
split.
- elim: t2 /; try by intros; rewrite subtermsE; set_solver.
  move=> t' t'' ts _ IH ?; rewrite subtermsE.
  do 2![rewrite elem_of_union; right].
  rewrite elem_of_union_list; exists (subterms t''); split => //.
  by rewrite elem_of_list_fmap; eauto.
- elim: t2; try by solve_subtermsP.
  move=> t IHt ts IHts _.
  rewrite subtermsE !elem_of_union elem_of_union_list elem_of_singleton.
  case=> [-> | [/IHt ?|sub]]; eauto using subterm.
  case: sub => _ [] /elem_of_list_fmap [] t' [] -> t'_ts sub.
  suffices: subterm t1 t' by eauto using subterm.
  elim: {t IHt} ts IHts t'_ts sub => /= [_|t ts IH [IHt IHts]].
    by rewrite elem_of_nil.
  by rewrite elem_of_cons; case => [->|?] //; eauto.
Qed.

Ltac solve_nonces_of_termP :=
  intros;
  repeat match goal with
  | H : context[nonces_of_term (?X ?Y)] |- _ =>
      rewrite [nonces_of_term (X Y)]nonces_of_termE /= in H
  | H : _ ∈ {[_]} |- _ =>
      rewrite elem_of_singleton in H;
      rewrite {}H
  | H : _ ∈ _ ∪ _ |- _ =>
      rewrite elem_of_union in H;
      destruct H
  | H : _ ∈ ∅ |- _ =>
      rewrite elem_of_empty in H;
      destruct H
  | H1 : ?P, H2 : ?P -> ?Q |- _ =>
      move/(_ H1) in H2
  end;
  eauto using subterm.

Lemma nonces_of_termP a t : subterm (TNonce a) t ↔ a ∈ nonces_of_term t.
Proof.
split.
- elim: t /; try by intros; rewrite nonces_of_termE; set_solver.
  move=> t t' ts _ IH t'_ts.
  rewrite nonces_of_termE elem_of_union; right.
  rewrite elem_of_union_list; exists (nonces_of_term t'); split => //.
  by rewrite elem_of_list_fmap; eauto.
- elim: t; try by solve_nonces_of_termP.
  move=> t IHt ts IHts _.
  rewrite nonces_of_termE !elem_of_union elem_of_union_list.
  case=> [/IHt ?|sub]; eauto using subterm.
  case: sub => _ [] /elem_of_list_fmap [] t' [] -> t'_ts sub.
  suffices: subterm (TNonce a) t' by eauto using subterm.
  elim: {t IHt} ts IHts t'_ts sub => /= [_|t ts IH [IHt IHts]].
    by rewrite elem_of_nil.
  by rewrite elem_of_cons; case => [->|?] //; eauto.
Qed.

Module Spec.

Implicit Types N : namespace.

Definition tag_def N (t : term) :=
  TPair (TInt (Zpos (encode N))) t.
Definition tag_aux : seal tag_def. by eexists. Qed.
Definition tag := unseal tag_aux.
Lemma tag_unseal : tag = tag_def. Proof. exact: seal_eq. Qed.

Definition untag_def N (t : term) :=
  match t with
  | TPair (TInt (Zpos m)) t =>
    if decide (encode N = m) then Some t else None
  | _ => None
  end.
Definition untag_aux : seal untag_def. by eexists. Qed.
Definition untag := unseal untag_aux.
Lemma untag_unseal : untag = untag_def. Proof. exact: seal_eq. Qed.

Lemma tagK N t : untag N (tag N t) = Some t.
Proof.
rewrite untag_unseal tag_unseal /untag_def /tag_def /=.
by rewrite decide_True_pi.
Qed.

#[global]
Instance tag_inj : Inj2 (=) (=) (=) tag.
Proof.
rewrite tag_unseal /tag_def => c1 t1 c2 t2 [] e ->.
split=> //; by apply: inj e.
Qed.

Lemma untagK N t1 t2 :
  untag N t1 = Some t2 ->
  t1 = tag N t2.
Proof.
rewrite untag_unseal tag_unseal /=.
case: t1=> [] // [] // [] //= m.
by case: decide => // <- _ [->].
Qed.

Lemma untag_tag_ne N1 N2 t :
  N1 ≠ N2 →
  Spec.untag N1 (Spec.tag N2 t) = None.
Proof.
move=> neq; rewrite Spec.untag_unseal Spec.tag_unseal /=.
rewrite decide_False //.
move=> eq_enc; apply: neq.
by apply: encode_inj eq_enc.
Qed.

Variant untag_spec N t : option term → Type :=
| UntagSome t' of t = Spec.tag N t' : untag_spec N t (Some t')
| UntagNone of (∀ t', t ≠ Spec.tag N t') : untag_spec N t None.

Lemma untagP N t : untag_spec N t (Spec.untag N t).
Proof.
case e: (Spec.untag N t) => [t'|]; constructor.
- by rewrite (Spec.untagK _ _ _ e).
- move=> t' e'; by rewrite e' Spec.tagK in e.
Qed.

Definition to_int t :=
  if t is TInt n then Some n else None.

Variant to_int_spec t : option Z → Type :=
| AsIntSome n of t = TInt n : to_int_spec t (Some n)
| AsIntNone of (∀ n, t ≠ TInt n) : to_int_spec t None.

Lemma to_intP t : to_int_spec t (Spec.to_int t).
Proof. by case: t => *; constructor; congruence. Qed.

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

Definition enc k t : term :=
  match k with
  | TKey Enc k => TEnc k t
  | _ => t (* Arbitrarily *)
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

Variant is_key_spec t : option key_type → Type :=
| IsKeySome kt k of t = TKey kt k : is_key_spec t (Some kt)
| IsKeyNone of (∀ kt k, t ≠ TKey kt k) : is_key_spec t None.

Lemma is_keyP t : is_key_spec t (is_key t).
Proof.
case: t; try by right.
by move=> kt t; eleft.
Qed.

Definition to_ek t :=
  if t is TKey Enc _ then Some t else None.

Variant to_ek_spec t : option term → Type :=
| ToEKSome k of t = TKey Enc k : to_ek_spec t (Some t)
| ToEKNone of (∀ k, t ≠ TKey Enc k) : to_ek_spec t None.

Lemma to_ekP t : to_ek_spec t (to_ek t).
Proof.
case: t; try by right.
case; try by right.
by move=> t; eleft.
Qed.

Definition to_dk t :=
  if t is TKey Dec _ then Some t else None.

Variant to_dk_spec t : option term → Type :=
| ToDKSome k of t = TKey Dec k : to_dk_spec t (Some t)
| ToDKNone of (∀ k, t ≠ TKey Dec k) : to_dk_spec t None.

Lemma to_dkP t : to_dk_spec t (to_dk t).
Proof.
case: t; try by right.
case; try by right.
by move=> t; eleft.
Qed.

Definition of_list_aux : seal (foldr TPair (TInt 0)). by eexists. Qed.
Definition of_list := unseal of_list_aux.
Lemma of_list_unseal : of_list = foldr TPair (TInt 0).
Proof. exact: seal_eq. Qed.

Definition mkskey t := TPair (TKey Enc t) (TKey Dec t).

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
Proof. rewrite of_list_unseal; by elim: l => //= t l ->. Qed.

Lemma to_listK t ts :
  to_list t = Some ts →
  t = of_list ts.
Proof.
rewrite of_list_unseal /=; elim/term_ind': t ts => //.
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

Lemma tdecK c k t t' :
  tdec c (TKey Dec k) t = Some t' →
  t = TEnc k (tag c t').
Proof.
rewrite /Spec.tdec /=.
case: t => [] //= k' t.
by case: decide => //= <- /Spec.untagK ->.
Qed.

Definition tsenc c k t :=
  match k with
  | TPair k _ => tenc c k t
  | _ => t
  end.

Definition tsdec c k t :=
  match k with
  | TPair _ k => tdec c k t
  | _ => None
  end.

Definition texp t1 t2 :=
  if t1 is TExp' base exp _ then
    TExp base (t2 :: map fold_term exp)
  else TInt 0.

Lemma texpA t1 ts1 t2 : texp (TExp t1 ts1) t2 = TExp t1 (t2 :: ts1).
Proof.
rewrite /texp [in TExp t1 ts1]unlock /= {1}[fold_term]unlock /=.
rewrite fold_wf_termE normalize_unfold1 normalize_unfoldn unfold_termK.
apply: TExp_perm. rewrite seq.perm_cons -{2}[ts1](seq.mapK unfold_termK).
by rewrite seq.perm_map // path.perm_sort.
Qed.

Lemma is_expP t : reflect (∃ t' ts, t = TExp t' ts) (is_exp t).
Proof.
apply/iff_reflect; split.
- case=> [] t' [] ts ->; apply: is_exp_TExp.
- elim: t => // t _ ts _ _ _; eauto.
Qed.

Lemma is_expN_texp t1 t2 : ~ is_exp t1 -> texp t1 t2 = TInt 0.
Proof. by case: t1. Qed.

Lemma unfold_exp t1 t2 :
  unfold_term (texp t1 t2) = PreTerm.exp (unfold_term t1) (unfold_term t2).
Proof.
case: t1 => //= t1 ts1 /(ssrbool.elimT ssrbool.andP) [wf_ts1 ?].
rewrite unfold_TExp /=; congr PreTerm.PTExp.
apply: (ssrbool.elimT (perm_sort_leP _ _ _ _)); rewrite seq.perm_cons.
rewrite -[@List.map]/@seq.map -seq.map_comp seq.map_id_in //= => {}t1 in_ts1.
by rewrite fold_termK // (ssrbool.elimT seq.allP wf_ts1).
Qed.

Definition zero : term := TInt 0.

End Spec.

Arguments repr_term /.
Arguments Spec.tag_def /.
Arguments Spec.untag_def /.

#[global]
Existing Instance Spec.of_list_inj.

Lemma subterm_tag c t1 t2 : subterm t1 t2 → subterm t1 (Spec.tag c t2).
Proof. by rewrite Spec.tag_unseal; eauto using subterm. Qed.

#[global]
Hint Resolve STRefl : core.
