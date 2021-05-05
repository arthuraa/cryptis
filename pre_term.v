From mathcomp Require Import all_ssreflect.
From deriving Require Import deriving.
From crypto Require Import mathcomp_compat lib.
Require Import Coq.ZArith.ZArith.
From iris.heap_lang Require Import locations.

Import Order.POrderTheory Order.TotalTheory.

Inductive key_type := Enc | Dec.

Canonical key_type_indDef := [indDef for key_type_rect].
Canonical key_type_indType := IndType key_type key_type_indDef.
Definition key_type_eqMixin := [derive eqMixin for key_type].
Canonical key_type_eqType := EqType key_type key_type_eqMixin.
Definition key_type_choiceMixin := [derive choiceMixin for key_type].
Canonical key_type_choiceType :=
  Eval hnf in ChoiceType key_type key_type_choiceMixin.
Definition key_type_countMixin := [derive countMixin for key_type].
Canonical key_type_countType :=
  Eval hnf in CountType key_type key_type_countMixin.
Definition key_type_orderMixin :=
  [derive orderMixin for key_type].
Canonical key_type_porderType :=
  Eval hnf in POrderType tt key_type key_type_orderMixin.
Canonical key_type_latticeType :=
  Eval hnf in LatticeType key_type key_type_orderMixin.
Canonical key_type_distrLatticeType :=
  Eval hnf in DistrLatticeType key_type key_type_orderMixin.
Canonical key_type_orderType :=
  Eval hnf in OrderType key_type key_type_orderMixin.

Module PreTerm.

Unset Elimination Schemes.
Inductive pre_term :=
| PTInt of Z
| PTPair of pre_term & pre_term
| PTNonce of loc
| PTKey of key_type & pre_term
| PTEnc of pre_term & pre_term
| PTHash of pre_term
| PTExp of pre_term & list pre_term.
Set Elimination Schemes.

Definition pre_term_rect'
  (T1 : pre_term -> Type)
  (T2 : list pre_term -> Type)
  (H1 : forall n, T1 (PTInt n))
  (H2 : forall t1, T1 t1 -> forall t2, T1 t2 -> T1 (PTPair t1 t2))
  (H3 : forall l, T1 (PTNonce l))
  (H4 : forall kt t, T1 t -> T1 (PTKey kt t))
  (H5 : forall t1, T1 t1 -> forall t2, T1 t2 -> T1 (PTEnc t1 t2))
  (H6 : forall t, T1 t -> T1 (PTHash t))
  (H7 : forall t, T1 t -> forall ts, T2 ts -> T1 (PTExp t ts))
  (H8 : T2 [::])
  (H9 : forall t, T1 t -> forall ts, T2 ts -> T2 (t :: ts)) :=
  fix loop1 t {struct t} : T1 t :=
    match t with
    | PTInt n => H1 n
    | PTPair t1 t2 => H2 t1 (loop1 t1) t2 (loop1 t2)
    | PTNonce l => H3 l
    | PTKey kt t => H4 kt t (loop1 t)
    | PTEnc t1 t2 => H5 t1 (loop1 t1) t2 (loop1 t2)
    | PTHash t => H6 t (loop1 t)
    | PTExp t ts =>
      let fix loop2 ts {struct ts} : T2 ts :=
          match ts with
          | [::] => H8
          | t :: ts => H9 t (loop1 t) ts (loop2 ts)
          end in
      H7 t (loop1 t) ts (loop2 ts)
    end.

Definition list_pre_term_rect'
  (T1 : pre_term -> Type)
  (T2 : list pre_term -> Type)
  (H1 : forall n, T1 (PTInt n))
  (H2 : forall t1, T1 t1 -> forall t2, T1 t2 -> T1 (PTPair t1 t2))
  (H3 : forall l, T1 (PTNonce l))
  (H4 : forall kt t, T1 t -> T1 (PTKey kt t))
  (H5 : forall t1, T1 t1 -> forall t2, T1 t2 -> T1 (PTEnc t1 t2))
  (H6 : forall t, T1 t -> T1 (PTHash t))
  (H7 : forall t, T1 t -> forall ts, T2 ts -> T1 (PTExp t ts))
  (H8 : T2 [::])
  (H9 : forall t, T1 t -> forall ts, T2 ts -> T2 (t :: ts)) :=
  fix loop2 ts {struct ts} : T2 ts :=
    match ts with
    | [::] => H8
    | t :: ts =>
      H9 t (pre_term_rect' T1 T2 H1 H2 H3 H4 H5 H6 H7 H8 H9 t) ts (loop2 ts)
    end.

Combined Scheme pre_term_list_pre_term_rect
  from pre_term_rect', list_pre_term_rect'.

Definition pre_term_list_pre_term_indDef :=
  [indDef for pre_term_list_pre_term_rect].
Canonical pre_term_indType := IndType pre_term pre_term_list_pre_term_indDef.
Definition pre_term_eqMixin :=
  [derive eqMixin for pre_term].
Canonical pre_term_eqType :=
  Eval hnf in EqType pre_term pre_term_eqMixin.
Definition pre_term_choiceMixin :=
  [derive choiceMixin for pre_term].
Canonical pre_term_choiceType :=
  Eval hnf in ChoiceType pre_term pre_term_choiceMixin.
Definition pre_term_countMixin :=
  [derive countMixin for pre_term].
Canonical pre_term_countType :=
  Eval hnf in CountType pre_term pre_term_countMixin.
Definition pre_term_orderMixin :=
  [derive orderMixin for pre_term].
Canonical pre_term_porderType :=
  Eval hnf in POrderType tt pre_term pre_term_orderMixin.
Canonical pre_term_latticeType :=
  Eval hnf in LatticeType pre_term pre_term_orderMixin.
Canonical pre_term_distrLatticeType :=
  Eval hnf in DistrLatticeType pre_term pre_term_orderMixin.
Canonical pre_term_orderType :=
  Eval hnf in OrderType pre_term pre_term_orderMixin.

Definition pre_term_rect (T : pre_term -> Type)
  (H1 : forall n, T (PTInt n))
  (H2 : forall t1, T t1 -> forall t2, T t2 -> T (PTPair t1 t2))
  (H3 : forall l, T (PTNonce l))
  (H4 : forall kt t, T t -> T (PTKey kt t))
  (H5 : forall t1, T t1 -> forall t2, T t2 -> T (PTEnc t1 t2))
  (H6 : forall t, T t -> T (PTHash t))
  (H7 : forall t, T t ->
        forall ts, foldr (fun t R => T t * R)%type unit ts ->
          T (PTExp t ts)) t : T t.
Proof.
exact: (@pre_term_rect' T (foldr (fun t R => T t * R)%type unit)).
Defined.

Definition pre_term_ind (T : pre_term -> Prop) :=
  @pre_term_rect T.

Fixpoint height pt :=
  match pt with
  | PTInt _ => 1
  | PTPair t1 t2 => S (maxn (height t1) (height t2))
  | PTNonce _ => 1
  | PTKey _ t => S (height t)
  | PTEnc k t => S (maxn (height k) (height t))
  | PTHash t => S (height t)
  | PTExp t ts => S (\max_(x <- height t :: map height ts) x)
  end.

Definition is_exp pt := if pt is PTExp _ _ then true else false.

Definition exp pt pts :=
  match pt with
  | PTExp pt pts' => PTExp pt (sort <=%O (pts' ++ pts))
  | _ => PTExp pt (sort <=%O pts)
  end.

Variant exp_spec pt pts : pre_term -> Type :=
| PTExpExp pt' pts' of pt = PTExp pt' pts'
: exp_spec pt pts (PTExp pt' (sort <=%O (pts' ++ pts)))

| PTExpNExp of exp pt pts = PTExp pt (sort <=%O pts)
& ~~ is_exp pt
: exp_spec pt pts (PTExp pt (sort <=%O pts)).

Lemma expP pt pts : exp_spec pt pts (exp pt pts).
Proof. by case: pt=> /= *; constructor. Qed.

(* An alternative of the above that avoids relying on mathcomp definitions *)
Variant exp_spec' pt pts : pre_term -> Type :=
| PTExpExp' pt' pts' pts'' of pt = PTExp pt' pts'
& Permutation.Permutation pts'' (List.app pts' pts)
: exp_spec' pt pts (PTExp pt' pts'')

| PTExpNExp' pts' of exp pt pts = PTExp pt pts'
& Permutation.Permutation pts' pts
: exp_spec' pt pts (PTExp pt pts').

Lemma expP' pt pts : exp_spec' pt pts (exp pt pts).
Proof.
by case: expP=> [? ? ->|? ?]; [eleft|eright]; eauto;
apply/perm_Permutation; rewrite perm_sort.
Qed.

Fixpoint normalize pt :=
  match pt with
  | PTInt n => PTInt n
  | PTPair t1 t2 => PTPair (normalize t1) (normalize t2)
  | PTNonce a => PTNonce a
  | PTKey kt t => PTKey kt (normalize t)
  | PTEnc k t => PTEnc (normalize k) (normalize t)
  | PTHash t => PTHash (normalize t)
  | PTExp t ts =>
    let t  := normalize t in
    let ts := [seq normalize t | t <- ts] in
    exp t ts
  end.

Fixpoint wf_term pt :=
  match pt with
  | PTInt _ => true
  | PTPair pt1 pt2 => wf_term pt1 && wf_term pt2
  | PTNonce _ => true
  | PTKey _ pt => wf_term pt
  | PTEnc k pt => wf_term k && wf_term pt
  | PTHash pt => wf_term pt
  | PTExp pt pts =>
    [&& ~~ is_exp pt, wf_term pt, all wf_term pts & sorted <=%O pts]
  end.

Lemma wf_exp pt pts : wf_term pt -> all wf_term pts -> wf_term (exp pt pts).
Proof.
case: expP => [pt' pts' ->|] /=.
- case/and4P=> -> -> norm_pts' _ /=.
  by rewrite all_sort all_cat norm_pts' /= sort_le_sorted => ->.
- by move=> _ -> -> /=; rewrite sort_le_sorted andbT all_sort.
Qed.

Lemma wf_normalize pt : wf_term (normalize pt).
Proof.
move: {2}(height pt) (leqnn (height pt)) => n.
elim: n pt => [[] //|n IH]; case=> //=.
- by move=> pt1 pt2; rewrite ltnS geq_max; case/andP=> /IH -> /IH ->.
- by move=> pt1 pt2; rewrite ltnS geq_max; case/andP=> /IH -> /IH ->.
move=> pt pts; rewrite ltnS big_cons geq_max big_map_id big_tnth.
case/andP => /IH e_pt /bigmax_leqP e_pts; rewrite wf_exp //.
rewrite all_map -[pts]in_tupleE; apply/allP => pt' /tnthP [] ? ->.
apply: IH; exact: e_pts.
Qed.

Lemma normalize_wf pt : wf_term pt -> normalize pt = pt.
Proof.
move: {2}(height pt) (leqnn (height pt)) => n.
elim: n pt => [[] //|n IH]; case=> //=.
- move=> pt1 pt2; rewrite ltnS geq_max.
  case/andP=> pt1_n pt2_n; case/andP=> norm_pt1 norm_pt2.
  by rewrite !IH.
- by move=> kt p; rewrite ltnS => ? ?; rewrite IH.
- move=> pt1 pt2; rewrite ltnS geq_max.
  case/andP=> pt1_n pt2_n; case/andP=> norm_pt1 norm_pt2.
  by rewrite !IH.
- by move=> p; rewrite ltnS => ? ?; rewrite IH.
move=> pt pts; rewrite ltnS big_cons geq_max big_map_id big_tnth.
case/andP => /IH e_pt /bigmax_leqP e_pts.
have {}e_pts pt': pt' \in in_tuple pts -> wf_term pt' -> normalize pt' = pt'.
  by case/tnthP=> ? ->; apply: IH; apply: e_pts.
case/and4P=> nexp norm_pt /allP norm_pts sort_pts.
rewrite e_pt // map_id_in; last first.
  by move=> ? in_pts; apply: e_pts (in_pts) _; apply: norm_pts.
by case: expP nexp=> [pt' pts' -> //|_ _ _]; rewrite sort_le_id.
Qed.

Lemma normalize_idem pt : normalize (normalize pt) = normalize pt.
Proof. apply: normalize_wf; exact: wf_normalize. Qed.

End PreTerm.

Canonical PreTerm.pre_term_eqType.
Canonical PreTerm.pre_term_choiceType.
Canonical PreTerm.pre_term_countType.
Canonical PreTerm.pre_term_porderType.
Canonical PreTerm.pre_term_latticeType.
Canonical PreTerm.pre_term_distrLatticeType.
Canonical PreTerm.pre_term_orderType.

Record term := Term_ {
  val_term : PreTerm.pre_term;
  _ : PreTerm.wf_term val_term;
}.

Canonical term_subType := [subType for val_term].
Definition term_eqMixin := [eqMixin of term by <:].
Canonical term_eqType := EqType term term_eqMixin.
Definition term_choiceMixin := [choiceMixin of term by <:].
Canonical term_choiceType := Eval hnf in ChoiceType term term_choiceMixin.
Definition term_countMixin := [countMixin of term by <:].
Canonical term_countType := Eval hnf in CountType term term_countMixin.
Definition term_porderMixin := [porderMixin of term by <:].
Canonical term_porderType :=
  Eval hnf in POrderType tt term term_porderMixin.
Definition term_orderMixin := [totalOrderMixin of term by <:].
Canonical term_latticeType :=
  Eval hnf in LatticeType term term_orderMixin.
Canonical term_distrLatticeType :=
  Eval hnf in DistrLatticeType term term_orderMixin.
Canonical term_orderType :=
  Eval hnf in OrderType term term_orderMixin.

Fact Term_key : unit. Proof. exact: tt. Qed.
Definition Term :=
  locked_with Term_key (
    fun t => @Term_ (PreTerm.normalize t) (PreTerm.wf_normalize t)
  ).
Canonical Term_unlockable := [unlockable of Term].

Implicit Types (t k : term) (ts : seq term).

Definition TInt n := Term (PreTerm.PTInt n).
Definition TPair t1 t2 := Term (PreTerm.PTPair (val t1) (val t2)).
Definition TNonce a := Term (PreTerm.PTNonce a).
Definition TKey kt t := Term (PreTerm.PTKey kt (val t)).
Definition TEnc k t := Term (PreTerm.PTEnc (val k) (val t)).
Definition THash t := Term (PreTerm.PTHash (val t)).
Definition TExp t ts := Term (PreTerm.PTExp (val t) [seq val t | t <- ts]).

Lemma val_termK : cancel val_term Term.
Proof.
case/SubP=> pt wf_pt; rewrite unlock; apply: val_inj.
exact: PreTerm.normalize_wf.
Qed.

Lemma val_term_TInt n : val_term (TInt n) = PreTerm.PTInt n.
Proof. by rewrite /TInt unlock. Qed.

Lemma val_term_TPair t1 t2 :
  val_term (TPair t1 t2) = PreTerm.PTPair (val_term t1) (val_term t2).
Proof. by rewrite /TPair unlock /= !PreTerm.normalize_wf ?valP. Qed.

Lemma val_term_TNonce a : val_term (TNonce a) = PreTerm.PTNonce a.
Proof. by rewrite /TNonce unlock. Qed.

Lemma val_term_TKey kt t : val_term (TKey kt t) = PreTerm.PTKey kt (val_term t).
Proof. by rewrite /TKey unlock /= PreTerm.normalize_wf ?valP. Qed.

Lemma val_term_TEnc k t :
  val_term (TEnc k t) = PreTerm.PTEnc (val_term k) (val_term t).
Proof. by rewrite /TEnc unlock /= !PreTerm.normalize_wf ?valP. Qed.

Lemma val_term_THash t :
  val_term (THash t) = PreTerm.PTHash (val_term t).
Proof. by rewrite /THash unlock /= !PreTerm.normalize_wf ?valP. Qed.

Lemma normalize_terms ts :
  map PreTerm.normalize (map val_term ts) = map val_term ts.
Proof.
rewrite map_id_in // => _ /mapP [] {}t t_ts ->.
apply: PreTerm.normalize_wf; apply: valP.
Qed.

Lemma val_term_TExp t ts :
  val_term (TExp t ts) = PreTerm.exp (val_term t) (List.map val_term ts).
Proof.
by rewrite /TExp unlock /= PreTerm.normalize_wf ?valP // normalize_terms.
Qed.

Definition val_termE :=
  (val_term_TInt,
   val_term_TPair,
   val_term_TNonce,
   val_term_TKey,
   val_term_TEnc,
   val_term_THash,
   val_term_TExp).

Lemma Term_PTInt n : Term (PreTerm.PTInt n) = TInt n.
Proof. by []. Qed.

Lemma Term_PTPair pt1 pt2 :
  Term (PreTerm.PTPair pt1 pt2) = TPair (Term pt1) (Term pt2).
Proof.
by apply: val_inj; rewrite /TPair unlock /= !PreTerm.normalize_idem.
Qed.

Lemma Term_PTNonce a : Term (PreTerm.PTNonce a) = TNonce a.
Proof. by []. Qed.

Lemma Term_PTKey kt pt : Term (PreTerm.PTKey kt pt) = TKey kt (Term pt).
Proof.
by apply: val_inj; rewrite /TKey unlock /= !PreTerm.normalize_idem.
Qed.

Lemma Term_PTEnc pt1 pt2 :
  Term (PreTerm.PTEnc pt1 pt2) = TEnc (Term pt1) (Term pt2).
Proof.
by apply: val_inj; rewrite /TEnc unlock /= !PreTerm.normalize_idem.
Qed.

Lemma Term_PTHash pt : Term (PreTerm.PTHash pt) = THash (Term pt).
Proof.
by apply: val_inj; rewrite /THash unlock /= !PreTerm.normalize_idem.
Qed.

Lemma Term_PTExp pt pts :
  Term (PreTerm.PTExp pt pts) = TExp (Term pt) (map Term pts).
Proof.
apply: val_inj; rewrite /TExp unlock /= PreTerm.normalize_idem.
by rewrite normalize_terms -map_comp.
Qed.

Definition TermE :=
  (Term_PTInt,
   Term_PTPair,
   Term_PTNonce,
   Term_PTKey,
   Term_PTEnc,
   Term_PTHash,
   Term_PTExp).

Lemma perm_sort_leP d (T : orderType d) (s1 s2 : seq T) :
  reflect (sort <=%O s1 = sort <=%O s2) (perm_eq s1 s2).
Proof.
apply/perm_sortP; by [apply: le_total|apply: le_trans|apply: le_anti].
Qed.

Lemma TExpA t ts1 ts2 : TExp (TExp t ts1) ts2 = TExp t (ts1 ++ ts2)%list.
Proof.
apply: val_inj => /=; rewrite !val_termE -[List.map]/@map map_cat.
case: (PreTerm.expP (val_term t)) => [pt' pts' e_t|_ nexp] /=.
  rewrite e_t /=; congr PreTerm.PTExp.
  by apply/perm_sort_leP; rewrite catA perm_cat2r perm_sort.
case: PreTerm.expP nexp => [? ? -> //|_ _ _].
by congr PreTerm.PTExp; apply/perm_sort_leP; rewrite perm_cat2r perm_sort.
Qed.

Lemma TExp_perm t ts1 ts2 : perm_eq ts1 ts2 -> TExp t ts1 = TExp t ts2.
Proof.
move=> perm_ts12; apply: val_inj => /=.
rewrite !val_termE -[List.map]/@map.
case: PreTerm.expP => [pt' pts' ->|_ nexp] /=.
  by congr PreTerm.PTExp; apply/perm_sort_leP; rewrite perm_cat2l perm_map.
case: PreTerm.expP nexp => [? ? -> //|_ _ _].
by congr PreTerm.PTExp; apply/perm_sort_leP; rewrite perm_map.
Qed.

Definition is_exp t := PreTerm.is_exp (val_term t).

Lemma term_rect (T : term -> Type)
  (H1 : forall n, T (TInt n))
  (H2 : forall t1, T t1 ->
        forall t2, T t2 ->
        T (TPair t1 t2))
  (H3 : forall a, T (TNonce a))
  (H4 : forall kt t, T t -> T (TKey kt t))
  (H5 : forall k, T k -> forall t, T t -> T (TEnc k t))
  (H6 : forall t, T t -> T (THash t))
  (H7 : forall t, T t -> ~~ is_exp t ->
        forall ts, foldr (fun t R => T t * R)%type unit ts ->
                   sorted <=%O ts ->
        T (TExp t ts)) :
  forall t, T t.
Proof.
move=> t; move: (valP t); rewrite -{2}[t]val_termK /=.
elim: (val_term t) => {t};
do ?by move=> *; rewrite /= TermE; eauto.
- by move=> t1 IH1 t2 IH2 /= /andP [] ??; rewrite TermE; eauto.
- by move=> t1 IH1 t2 IH2 /= /andP [] ??; rewrite TermE; eauto.
move=> t IHt ts IHts; rewrite TermE /=.
case/and4P=> nexp wf_t wf_ts sorted_ts; apply: H7; eauto.
- by rewrite /is_exp unlock /= PreTerm.normalize_wf.
- elim: ts IHts wf_ts {sorted_ts} => //= {IHt nexp wf_t}t ts IH [??].
  by case/andP=> wf_t wf_ts; split; eauto.
have e_ts: ts = map val_term (map Term ts).
  rewrite -map_comp map_id_in // => t' t'_ts.
  rewrite unlock /= PreTerm.normalize_wf //.
  exact: (allP wf_ts).
by rewrite e_ts sorted_map in sorted_ts.
Qed.

Definition term_ind (P : term -> Prop) := @term_rect P.
