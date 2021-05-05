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

Lemma exp_nexp pt pts :
  ~~ is_exp pt ->
  exp pt pts = PTExp pt (sort <=%O pts).
Proof. by case: pt. Qed.

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

Unset Elimination Schemes.
Inductive term :=
| TInt of Z
| TPair of term & term
| TNonce of loc
| TKey of key_type & term
| TEnc of term & term
| THash of term
| TExp' pt pts of PreTerm.wf_term (PreTerm.PTExp pt pts).
Set Elimination Schemes.

(* We use a different name for the default induction scheme, as it does not
   allow us to recurse under exponentials.  Later, we'll prove term_ind, which
   does allow this. *)
Scheme term_ind' := Induction for term Sort Prop.

Fixpoint unfold_term t :=
  match t with
  | TInt n => PreTerm.PTInt n
  | TPair t1 t2 => PreTerm.PTPair (unfold_term t1) (unfold_term t2)
  | TNonce l => PreTerm.PTNonce l
  | TKey kt t => PreTerm.PTKey kt (unfold_term t)
  | TEnc k t => PreTerm.PTEnc (unfold_term k) (unfold_term t)
  | THash t => PreTerm.PTHash (unfold_term t)
  | TExp' pt pts _ => PreTerm.PTExp pt pts
  end.

Fixpoint fold_wf_term pt : PreTerm.wf_term pt -> term :=
  match pt with
  | PreTerm.PTInt n => fun _ => TInt n
  | PreTerm.PTPair pt1 pt2 => fun wf =>
    TPair (fold_wf_term pt1 (andP wf).1)
          (fold_wf_term pt2 (andP wf).2)
  | PreTerm.PTNonce l => fun _ => TNonce l
  | PreTerm.PTKey kt pt => fun wf => TKey kt (fold_wf_term pt wf)
  | PreTerm.PTEnc k pt => fun wf =>
    TEnc (fold_wf_term k (andP wf).1)
         (fold_wf_term pt (andP wf).2)
  | PreTerm.PTHash pt => fun wf =>
    THash (fold_wf_term pt wf)
  | PreTerm.PTExp pt' pts' => fun wf =>
    TExp' pt' pts' wf
  end.

Lemma wf_unfold_term t : PreTerm.wf_term (unfold_term t).
Proof. by elim/term_ind': t=> //= ? -> ? ->. Qed.

Definition fold_term pt :=
  fold_wf_term _ (PreTerm.wf_normalize pt).

Lemma unfold_termK : cancel unfold_term fold_term.
Proof.
move=> t; rewrite /fold_term; move: (PreTerm.wf_normalize _).
rewrite PreTerm.normalize_wf ?wf_unfold_term //.
elim/term_ind': t => //=.
- by move=> t1 IH1 t2 IH2 wf; rewrite IH1 IH2.
- by move=> kt t IH wf; rewrite IH.
- by move=> t1 IH1 t2 IH2 wf; rewrite IH1 IH2.
- by move=> t IH wf; rewrite IH.
- move=> //= pt pts wf1 wf2.
  by rewrite (bool_irrelevance wf1 wf2).
Qed.

Lemma fold_termK pt : PreTerm.wf_term pt -> unfold_term (fold_term pt) = pt.
Proof.
move=> wf; rewrite /fold_term; move: (PreTerm.wf_normalize _).
rewrite PreTerm.normalize_wf // {wf}.
elim: pt => //=.
- by move=> pt1 IH1 pt2 IH2 wf; rewrite IH1 IH2.
- by move=> kt t IH wf; rewrite IH.
- by move=> pt1 IH1 pt2 IH2 wf; rewrite IH1 IH2.
- by move=> t IH wf; rewrite IH.
Qed.

Lemma fold_normalize pt : fold_term (PreTerm.normalize pt) = fold_term pt.
Proof.
rewrite /fold_term; move: (PreTerm.wf_normalize _) (PreTerm.wf_normalize _).
rewrite PreTerm.normalize_idem => wf1 wf2.
congr fold_wf_term; apply: bool_irrelevance.
Qed.

Lemma fold_wf_termE pt wf : fold_wf_term pt wf = fold_term pt.
Proof.
rewrite /fold_term; move: (PreTerm.wf_normalize _).
rewrite PreTerm.normalize_wf // => ?.
congr fold_wf_term; apply: bool_irrelevance.
Qed.

Lemma unfold_foldE pt : unfold_term (fold_term pt) = PreTerm.normalize pt.
Proof.
by rewrite -fold_normalize fold_termK // PreTerm.wf_normalize.
Qed.

Lemma unfold_term_inj : injective unfold_term.
Proof. exact: can_inj unfold_termK. Qed.

Implicit Types (t k : term) (ts : seq term).

Section TExp.

Fact TExp_key : unit. Proof. exact: tt. Qed.
Definition TExp :=
  locked_with TExp_key (
    fun t ts =>
      fold_term (PreTerm.PTExp (unfold_term t) (map unfold_term ts))
  ).
Canonical TExp_unlock := [unlockable of TExp].

End TExp.

Definition term_eqMixin := InjEqMixin unfold_term_inj.
Canonical term_eqType := EqType term term_eqMixin.
Definition term_choiceMixin := CanChoiceMixin unfold_termK.
Canonical term_choiceType := Eval hnf in ChoiceType term term_choiceMixin.
Definition term_countMixin := CanCountMixin unfold_termK.
Canonical term_countType := Eval hnf in CountType term term_countMixin.
Definition term_orderMixin := CanOrderMixin unfold_termK.
Canonical term_porderType :=
  Eval hnf in POrderType tt term term_orderMixin.
Canonical term_latticeType :=
  Eval hnf in LatticeType term term_orderMixin.
Canonical term_distrLatticeType :=
  Eval hnf in DistrLatticeType term term_orderMixin.
Canonical term_orderType :=
  Eval hnf in OrderType term term_orderMixin.

Lemma normalize_unfold1 t :
  PreTerm.normalize (unfold_term t) = unfold_term t.
Proof. by rewrite PreTerm.normalize_wf // wf_unfold_term. Qed.

Lemma normalize_unfoldn ts :
  map PreTerm.normalize (map unfold_term ts) = map unfold_term ts.
Proof.
rewrite map_id_in // => ? /mapP [] {}t t_ts ->.
exact: normalize_unfold1.
Qed.

Lemma unfold_TExp t ts :
  unfold_term (TExp t ts)
  = PreTerm.exp (unfold_term t) (List.map unfold_term ts).
Proof.
by rewrite unlock /= unfold_foldE /= normalize_unfold1 normalize_unfoldn.
Qed.

Lemma perm_sort_leP d (T : orderType d) (s1 s2 : seq T) :
  reflect (sort <=%O s1 = sort <=%O s2) (perm_eq s1 s2).
Proof.
apply/perm_sortP; by [apply: le_total|apply: le_trans|apply: le_anti].
Qed.

Lemma TExpA t ts1 ts2 : TExp (TExp t ts1) ts2 = TExp t (ts1 ++ ts2)%list.
Proof.
apply: unfold_term_inj.
rewrite !unfold_TExp /= -[List.map]/@map map_cat.
case: (PreTerm.expP (unfold_term t)) => [pt' pts' e_t|_ nexp] /=.
  rewrite e_t /=; congr PreTerm.PTExp.
  by apply/perm_sort_leP; rewrite catA perm_cat2r perm_sort.
case: PreTerm.expP nexp => [? ? -> //|_ _ _].
by congr PreTerm.PTExp; apply/perm_sort_leP; rewrite perm_cat2r perm_sort.
Qed.

Lemma TExp_perm t ts1 ts2 : perm_eq ts1 ts2 -> TExp t ts1 = TExp t ts2.
Proof.
move=> perm_ts12; apply: unfold_term_inj.
rewrite !unfold_TExp -[List.map]/@map.
case: PreTerm.expP => [pt' pts' ->|_ nexp] /=.
  by congr PreTerm.PTExp; apply/perm_sort_leP; rewrite perm_cat2l perm_map.
case: PreTerm.expP nexp => [? ? -> //|_ _ _].
by congr PreTerm.PTExp; apply/perm_sort_leP; rewrite perm_map.
Qed.

Definition is_exp t :=
  if t is TExp' _ _ _ then true else false.

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
move=> t; rewrite -(unfold_termK t) /fold_term.
move: (PreTerm.wf_normalize _); rewrite normalize_unfold1.
elim: (unfold_term t) => {t} /=; do ?by move=> * /=; eauto.
move=> pt IHpt pts IHpts wf.
case/and4P: {-}(wf) => nexp wf_pt wf_pts sorted_pts.
have [t e_pt] : {t | pt = unfold_term t}.
  by exists (fold_term pt); rewrite fold_termK.
rewrite {}e_pt {pt wf_pt} in IHpt wf nexp *.
have [ts e_pts] : {ts | pts = map unfold_term ts}.
  exists (map fold_term pts).
  rewrite -map_comp map_id_in // => pt' pt'_pts.
  by rewrite /= fold_termK // (allP wf_pts).
rewrite {}e_pts {pts wf_pts} in IHpts wf sorted_pts *.
rewrite (_ : TExp' _ _ _ = TExp t ts); last first.
  apply: unfold_term_inj => /=.
  by rewrite unfold_TExp PreTerm.exp_nexp // sort_le_id.
apply: H7.
- by move/(_ (wf_unfold_term _)): IHpt; rewrite fold_wf_termE unfold_termK.
- by case: (t) nexp => //= ? _ ->.
- elim: ts IHpts {wf sorted_pts} => /= [[] //|t' ts ? [] IHt IHts].
  split; last by eauto.
  rewrite -[t']unfold_termK -(fold_wf_termE _ (wf_unfold_term _)).
  exact: IHt.
- by move: sorted_pts; rewrite sorted_map.
Qed.

Definition term_ind (P : term -> Prop) := @term_rect P.
