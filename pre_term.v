From mathcomp Require Import all_ssreflect.
From deriving Require Import deriving.
From cryptis Require Import mathcomp_compat lib.
Require Import Coq.ZArith.ZArith Lia.
From iris.heap_lang Require locations.

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

Notation TInt_tag := 0%Z.
Notation TPair_tag := 1%Z.
Notation TNonce_tag := 2%Z.
Notation TKey_tag := 3%Z.
Notation TEnc_tag := 4%Z.
Notation THash_tag := 5%Z.
Notation TExp_tag := 6%Z.

Module PreTerm.

Unset Elimination Schemes.
Inductive pre_term :=
| PTInt of Z
| PTPair of pre_term & pre_term
| PTNonce of locations.loc
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

Definition seq_pre_term := seq pre_term.
Definition seq_pre_term_orderMixin :=
  [derive orderMixin for seq pre_term].
Canonical seq_pre_term_porderType :=
  Eval hnf in POrderType tt seq_pre_term seq_pre_term_orderMixin.
Canonical seq_pre_term_latticeType :=
  Eval hnf in LatticeType seq_pre_term seq_pre_term_orderMixin.
Canonical seq_pre_term_distrLatticeType :=
  Eval hnf in DistrLatticeType seq_pre_term seq_pre_term_orderMixin.
Canonical seq_pre_term_orderType :=
  Eval hnf in OrderType seq_pre_term seq_pre_term_orderMixin.

Definition cons_num pt : Z :=
  match pt with
  | PTInt _ => TInt_tag
  | PTPair _ _ => TPair_tag
  | PTNonce _ => TNonce_tag
  | PTKey _ _ => TKey_tag
  | PTEnc _ _ => TEnc_tag
  | PTHash _ => THash_tag
  | PTExp _ _ => TExp_tag
  end.

Open Scope order_scope.

Lemma leqE pt1 pt2 :
  (pt1 <= pt2)%O =
  if cons_num pt1 == cons_num pt2 then
    match pt1, pt2 with
    | PTInt n1, PTInt n2 => (n1 <= n2)%O
    | PTPair pt11 pt12, PTPair pt21 pt22 =>
      if pt11 == pt21 then (pt12 <= pt22)%O
      else (pt11 <= pt21)%O
    | PTNonce a1, PTNonce a2 => (a1 <= a2)%O
    | PTKey kt1 pt1, PTKey kt2 pt2 =>
      if kt1 == kt2 then (pt1 <= pt2)%O
      else (kt1 <= kt2)%O
    | PTEnc k1 pt1, PTEnc k2 pt2 =>
      if k1 == k2 then (pt1 <= pt2)%O
      else (k1 <= k2)%O
    | PTHash pt1, PTHash pt2 => (pt1 <= pt2)%O
    | PTExp pt1 pts1, PTExp pt2 pts2 =>
      if pt1 == pt2 then ((pts1 : seqlexi_with tt _) <= pts2)%O
      else (pt1 <= pt2)%O
    | _, _ => false
    end
  else (cons_num pt1 <=? cons_num pt2)%Z.
Proof.
have le_alt (T : orderType _) (x y : T) :
    (x <= y)%O = if x == y then true else (x <= y)%O.
  by case: (ltgtP x y).
case: pt1 pt2
    => [n1|pt11 pt12|a1|kt1 pt1|pt11 pt12|pt1|pt1 pts1]
       [n2|pt21 pt22|a2|kt2 pt2|pt21 pt22|pt2|pt2 pts2] //=.
- by rewrite [RHS]le_alt.
- by rewrite [(pt12 <= pt22)%O]le_alt.
- by rewrite [RHS]le_alt.
- by rewrite (le_alt _ _ pt1).
- by rewrite (le_alt _ _ pt12).
- by rewrite (le_alt _ _ pt1).
have -> : ((pts1 : seqlexi_with tt _) <= pts2)%O = ((pts1 : seq_pre_term) <= pts2)%O.
  elim: pts1 pts2 {pt1 pt2} => [|pt1 pts1 IH] [|pt2 pts2] //=.
    rewrite [LHS](_ : _ = if pt1 == pt2 then if pts1 == pts2 then true
                                             else ((pts1 : seq_pre_term) <= pts2)%O
                          else (pt1 <= pt2)%O) //.
    rewrite lexi_cons IH.
    case: ltgtP => //= _; exact: le_alt.
by rewrite [(pts1 : seq_pre_term)  <= pts2]le_alt.
Qed.

Close Scope order_scope.

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

Fixpoint size pt :=
  match pt with
  | PTInt _ => 1
  | PTPair pt1 pt2 => S (size pt1 + size pt2)
  | PTNonce _ => 1
  | PTKey _ t => S (size t)
  | PTEnc k t => S (S (size k) + size t)
  | PTHash t => S (size t)
  | PTExp t ts => S (\sum_(n <- size t :: map size ts) n)
  end.

Lemma size_gt0 pt : 0 < size pt. Proof. by case: pt. Qed.

Definition exp pt1 pt2 :=
  match pt1 with
  | PTExp pt1 pts1 => PTExp pt1 (sort <=%O (pt2 :: pts1))
  | _ => PTInt 0
  end.

Fixpoint normalize pt :=
  match pt with
  | PTInt n => PTInt n
  | PTPair t1 t2 => PTPair (normalize t1) (normalize t2)
  | PTNonce a => PTNonce a
  | PTKey kt t => PTKey kt (normalize t)
  | PTEnc k t => PTEnc (normalize k) (normalize t)
  | PTHash t => PTHash (normalize t)
  | PTExp t ts => PTExp (normalize t) (sort <=%O (map normalize ts))
  end.

Fixpoint wf_term pt :=
  match pt with
  | PTInt _ => true
  | PTPair pt1 pt2 => wf_term pt1 && wf_term pt2
  | PTNonce _ => true
  | PTKey _ pt => wf_term pt
  | PTEnc k pt => wf_term k && wf_term pt
  | PTHash pt => wf_term pt
  | PTExp pt pts => [&& wf_term pt, all wf_term pts & sorted <=%O pts]
  end.

Lemma wf_normalize pt : wf_term (normalize pt).
Proof.
move: {2}(height pt) (leqnn (height pt)) => n.
elim: n pt => [[] //|n IH]; case=> //=.
- by move=> pt1 pt2; rewrite ltnS geq_max; case/andP=> /IH -> /IH ->.
- by move=> pt1 pt2; rewrite ltnS geq_max; case/andP=> /IH -> /IH ->.
move=> pt pts; rewrite ltnS big_cons geq_max big_map_id big_tnth.
case/andP => /IH e_pt /bigmax_leqP e_pts.
rewrite e_pt /= sort_le_sorted andbT all_sort all_map -[pts]in_tupleE.
apply/allP => pt' /tnthP [] ? ->; apply: IH; exact: e_pts.
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
case/and3P=> norm_pt /allP norm_pts sort_pts.
rewrite e_pt // map_id_in ?sort_le_id // => ? in_pts.
by apply: e_pts (in_pts) _; apply: norm_pts.
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
| TNonce of locations.loc
| TKey of key_type & term
| TEnc of term & term
| THash of term
| TExp' (t : term) pts of all PreTerm.wf_term pts && sorted <=%O pts.
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
  | TExp' t pts _ => PreTerm.PTExp (unfold_term t) pts
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
    let t := fold_wf_term pt' (andP wf).1 in
    TExp' t pts' (andP wf).2
  end.

Lemma wf_unfold_term t : PreTerm.wf_term (unfold_term t).
Proof. by elim/term_ind': t=> //= ? -> ? ->. Qed.

Fact fold_term_key : unit. Proof. exact: tt. Qed.
Definition fold_term :=
  locked_with fold_term_key (fun pt =>
    fold_wf_term _ (PreTerm.wf_normalize pt)).
Canonical fold_term_unlockable := [unlockable of fold_term].

Lemma unfold_termK : cancel unfold_term fold_term.
Proof.
move=> t; rewrite [fold_term]unlock; move: (PreTerm.wf_normalize _).
rewrite PreTerm.normalize_wf ?wf_unfold_term //.
elim/term_ind': t => //=.
- by move=> t1 IH1 t2 IH2 wf; rewrite IH1 IH2.
- by move=> kt t IH wf; rewrite IH.
- by move=> t1 IH1 t2 IH2 wf; rewrite IH1 IH2.
- by move=> t IH wf; rewrite IH.
- move=> //= t IH pts wf1 wf2.
  rewrite IH; apply: congr1; apply: bool_irrelevance.
Qed.

Lemma fold_termK pt : PreTerm.wf_term pt -> unfold_term (fold_term pt) = pt.
Proof.
move=> wf; rewrite [fold_term]unlock; move: (PreTerm.wf_normalize _).
rewrite PreTerm.normalize_wf // {wf}.
elim: pt => //=.
- by move=> pt1 IH1 pt2 IH2 wf; rewrite IH1 IH2.
- by move=> kt t IH wf; rewrite IH.
- by move=> pt1 IH1 pt2 IH2 wf; rewrite IH1 IH2.
- by move=> t IH wf; rewrite IH.
- by move=> pt IHpt pts IHpts wf; rewrite IHpt.
Qed.

Lemma fold_normalize pt : fold_term (PreTerm.normalize pt) = fold_term pt.
Proof.
rewrite [fold_term]unlock; move: (PreTerm.wf_normalize _) (PreTerm.wf_normalize _).
rewrite PreTerm.normalize_idem => wf1 wf2.
congr fold_wf_term; apply: bool_irrelevance.
Qed.

Lemma fold_wf_termE pt wf : fold_wf_term pt wf = fold_term pt.
Proof.
rewrite [fold_term]unlock; move: (PreTerm.wf_normalize _).
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
  = PreTerm.PTExp (unfold_term t) (sort <=%O (List.map unfold_term ts)).
Proof.
by rewrite unlock unfold_foldE /= normalize_unfold1 normalize_unfoldn.
Qed.

Variant unfold_TExp_spec t ts : PreTerm.pre_term -> Type :=
| UnfoldTExp pts'
  of Permutation.Permutation pts' (map unfold_term ts)
: unfold_TExp_spec t ts (PreTerm.PTExp (unfold_term t) pts').

Lemma unfold_TExpP t ts : unfold_TExp_spec t ts (unfold_term (TExp t ts)).
Proof.
rewrite unfold_TExp; constructor.
apply/perm_Permutation.
by rewrite perm_sort.
Qed.

Lemma fold_termE pt :
  fold_term pt =
  match pt with
  | PreTerm.PTInt n => TInt n
  | PreTerm.PTPair pt1 pt2 => TPair (fold_term pt1) (fold_term pt2)
  | PreTerm.PTNonce l => TNonce l
  | PreTerm.PTKey kt pt => TKey kt (fold_term pt)
  | PreTerm.PTEnc pt1 pt2 => TEnc (fold_term pt1) (fold_term pt2)
  | PreTerm.PTHash pt => THash (fold_term pt)
  | PreTerm.PTExp pt pts => TExp (fold_term pt) (List.map fold_term pts)
  end.
Proof.
apply/unfold_term_inj. rewrite [fold_term]unlock.
case: pt =>> //=;
rewrite ?unfold_TExp !fold_wf_termE !unfold_foldE !PreTerm.normalize_idem //.
congr (PreTerm.PTExp _ (sort _ _)).
rewrite -[@List.map]/(@map) -map_comp.
by under [in RHS]eq_map => ?
  do rewrite /= fold_wf_termE unfold_foldE PreTerm.normalize_idem.
Qed.

Lemma TExp_perm t ts1 ts2 : perm_eq ts1 ts2 -> TExp t ts1 = TExp t ts2.
Proof.
move=> perm_ts12; apply: unfold_term_inj.
rewrite !unfold_TExp -[List.map]/@map.
by congr PreTerm.PTExp; apply/perm_sort_leP; rewrite perm_map.
Qed.

Lemma TExpC t ts1 ts2 : TExp t (ts1 ++ ts2) = TExp t (ts2 ++ ts1).
Proof. by apply: TExp_perm; rewrite perm_catC. Qed.

Definition is_exp t :=
  if t is TExp' _ _ _ then true else false.

Lemma is_exp_TExp t ts : is_exp (TExp t ts).
Proof. by rewrite unlock [fold_term]unlock /=. Qed.

Definition tsize t := PreTerm.size (unfold_term t).

Lemma tsize_gt0 t : 0 < tsize t. Proof. exact: PreTerm.size_gt0. Qed.

Lemma tsize_TExp t ts :
  tsize (TExp t ts) = (sumn (tsize t :: map tsize ts)).+1.
Proof.
rewrite /tsize unfold_TExp /= -sumnE /=; congr (_ + _).+1.
apply: perm_sumn; rewrite [X in perm_eq _ X]map_comp perm_map //.
by rewrite perm_sort.
Qed.

Lemma TExp'E t pts wf : TExp' t pts wf = TExp t (map fold_term pts).
Proof.
apply: unfold_term_inj => /=; rewrite unfold_TExp -[@List.map]/@map.
case/andP: wf => wf_pts sorted_pts.
rewrite -map_comp map_id_in ?sort_le_id // => pt in_pts.
by rewrite /= fold_termK // (allP wf_pts).
Qed.

Lemma TExp_inj t1 ts1 t2 ts2 :
  TExp t1 ts1 = TExp t2 ts2 <->
  t1 = t2 /\ Permutation.Permutation ts1 ts2.
Proof.
split; last first.
  case=> -> /perm_Permutation; exact: TExp_perm.
move=> /(congr1 unfold_term); rewrite !unfold_TExp.
case=> /unfold_term_inj -> /perm_sort_leP/perm_map_inj/perm_Permutation perm.
split => //; apply: perm unfold_term_inj.
Qed.

Lemma TExp_inj1 t1 t1' t2 t2' :
  TExp t1 [:: t1'] = TExp t2 [:: t2'] <->
  t1 = t2 /\ t1' = t2'.
Proof.
rewrite TExp_inj; split => [[-> e]|[-> ->]] //; split => //.
by move: (Permutation.Permutation_length_1_inv e) => [->].
Qed.

Lemma tsize_eq t :
  tsize t =
  match t with
  | TInt _ => 1
  | TPair t1 t2 => S (tsize t1 + tsize t2)
  | TNonce _ => 1
  | TKey _ t => S (tsize t)
  | TEnc k t => S (S (tsize k) + tsize t)
  | THash t => S (tsize t)
  | TExp' t pts _ => S (tsize t + \sum_(n <- map PreTerm.size pts) n)
  end.
Proof.
case: t => //= t pts wf.
rewrite TExp'E tsize_TExp /= sumnE -map_comp.
case/andP: wf=> wf_pts _; congr (_ + bigop _ _ _).+1.
by apply/eq_in_map => pt in_pts /=; rewrite /tsize fold_termK // (allP wf_pts).
Qed.

Lemma tsize_TExp_lt t1 ts1 t2 :
  (tsize (TExp t1 ts1) < tsize (TExp t1 (t2 :: ts1)))%coq_nat /\
  (tsize t2 < tsize (TExp t1 (t2 :: ts1)))%coq_nat.
Proof.
rewrite !tsize_TExp /= -!plusE.
move/ssrnat.ltP: (tsize_gt0 t1) => pos_t1.
move/ssrnat.ltP: (tsize_gt0 t2) => pos_t2.
split; lia.
Qed.

Variant TExp_spec t ts : term -> Type :=
| TExpSpec pts' H & Permutation.Permutation pts' (List.map unfold_term ts)
: TExp_spec t ts (TExp' t pts' H).

Lemma TExpP t ts : TExp_spec t ts (TExp t ts).
Proof.
rewrite [TExp]unlock /= [fold_term]unlock /= fold_wf_termE.
rewrite fold_normalize unfold_termK.
move: (proj2 _); rewrite normalize_unfoldn.
set ts' := map unfold_term ts.
have: Permutation.Permutation (sort <=%O ts') ts'.
  by apply/perm_Permutation; rewrite perm_sort.
move: (sort _ _) => pts'' ? ?; by split.
Qed.

Lemma term_rect (T : term -> Type)
  (H1 : forall n, T (TInt n))
  (H2 : forall t1, T t1 ->
        forall t2, T t2 ->
        T (TPair t1 t2))
  (H3 : forall a, T (TNonce a))
  (H4 : forall kt t, T t -> T (TKey kt t))
  (H5 : forall k, T k -> forall t, T t -> T (TEnc k t))
  (H6 : forall t, T t -> T (THash t))
  (H7 : forall t, T t ->
        forall ts, foldr (fun t R => T t * R)%type unit ts ->
                   sorted <=%O ts ->
        T (TExp t ts)) :
  forall t, T t.
Proof.
move=> t; rewrite -(unfold_termK t) [fold_term]unlock.
move: (PreTerm.wf_normalize _); rewrite normalize_unfold1.
elim: (unfold_term t) => {t} /=; do ?by move=> * /=; eauto.
move=> pt IHpt pts IHpts wf.
case/and3P: {-}(wf) => wf_pt wf_pts sorted_pts.
have [t e_pt] : {t | pt = unfold_term t}.
  by exists (fold_term pt); rewrite fold_termK.
rewrite {}e_pt {pt wf_pt} in IHpt wf *.
have [ts e_pts] : {ts | pts = map unfold_term ts}.
  exists (map fold_term pts).
  rewrite -map_comp map_id_in // => pt' pt'_pts.
  by rewrite /= fold_termK // (allP wf_pts).
rewrite {}e_pts {pts wf_pts} in IHpts wf sorted_pts *.
rewrite (_ : TExp' _ _ _ = TExp t ts); last first.
  apply: unfold_term_inj.
  by rewrite fold_wf_termE unfold_termK unfold_TExp /= sort_le_id.
apply: H7.
- by move/(_ (wf_unfold_term _)): IHpt; rewrite fold_wf_termE unfold_termK.
- elim: ts IHpts {wf sorted_pts} => /= [[] //|t' ts ? [] IHt IHts].
  split; last by eauto.
  rewrite -[t']unfold_termK -(fold_wf_termE _ (wf_unfold_term _)).
  exact: IHt.
- by move: sorted_pts; rewrite sorted_map.
Qed.

Definition term_ind (P : term -> Prop) := @term_rect P.

Lemma term_lt_ind (T : term -> Prop) :
  (forall t, (forall t', (tsize t' < tsize t)%coq_nat -> T t') -> T t) ->
  forall t, T t.
Proof.
move=> H t.
move: {-1}(tsize t) (Nat.le_refl (tsize t)) => n.
elim: n / (lt_wf n) t => n _ IH t t_n.
apply: H => t' t'_t.
apply: (IH (tsize t')); lia.
Qed.
