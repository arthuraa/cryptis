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

Fixpoint tsize pt :=
  match pt with
  | PTInt _ => 1
  | PTPair pt1 pt2 => S (tsize pt1 + tsize pt2)
  | PTNonce _ => 1
  | PTKey _ t => S (tsize t)
  | PTEnc k t => S (S (tsize k) + tsize t)
  | PTHash t => S (tsize t)
  | PTExp t ts => S (\sum_(n <- tsize t :: map tsize ts) n)
  end.

Lemma tsize_gt0 pt : 0 < tsize pt. Proof. by case: pt. Qed.

Definition base pt := if pt is PTExp pt _   then pt  else pt.
Definition exps pt := if pt is PTExp pt pts then pts else [::].

Definition exp pt pts :=
  if size pts == 0 then pt
  else PTExp (base pt) (sort <=%O (exps pt ++ pts)).

Lemma tsize_exp t ts :
  tsize (exp t ts) =
  if ts == [::] then tsize t
  else S (\sum_(t' <- base t :: exps t ++ ts) tsize t').
Proof.
rewrite /exp [LHS]fun_if /= size_eq0.
have: perm_eq (sort <=%O (exps t ++ ts)) (exps t ++ ts) by rewrite perm_sort.
by move=> e; rewrite !big_cons !big_map (perm_big _ e).
Qed.

Definition is_exp pt :=
  if pt is PTExp _ _ then true else false.

Lemma base_expN pt : ~~ is_exp pt -> base pt = pt.
Proof. by case: pt. Qed.

Lemma exps_expN pt : ~~ is_exp pt -> exps pt = [::].
Proof. by case: pt. Qed.

Lemma base_expsK pt : is_exp pt -> PTExp (base pt) (exps pt) = pt.
Proof. by case: pt. Qed.

Lemma is_exp_exp pt pts : is_exp (exp pt pts) = (pts != [::]) || is_exp pt.
Proof. by rewrite /exp size_eq0; case: eqP. Qed.

Lemma perm_exp pt pts1 pts2 : perm_eq pts1 pts2 -> exp pt pts1 = exp pt pts2.
Proof.
move=> pts12; rewrite /exp (perm_size pts12); case: (_ == _) => //.
have /perm_sort_leP -> // : perm_eq (exps pt ++ pts1) (exps pt ++ pts2).
by rewrite perm_cat2l.
Qed.

Fixpoint normalize pt :=
  match pt with
  | PTInt n => PTInt n
  | PTPair t1 t2 => PTPair (normalize t1) (normalize t2)
  | PTNonce a => PTNonce a
  | PTKey kt t => PTKey kt (normalize t)
  | PTEnc k t => PTEnc (normalize k) (normalize t)
  | PTHash t => PTHash (normalize t)
  | PTExp t ts => exp (normalize t) (map normalize ts)
  end.

Fixpoint wf_term pt :=
  match pt with
  | PTInt _ => true
  | PTPair pt1 pt2 => wf_term pt1 && wf_term pt2
  | PTNonce _ => true
  | PTKey _ pt => wf_term pt
  | PTEnc k pt => wf_term k && wf_term pt
  | PTHash pt => wf_term pt
  | PTExp pt pts => [&& wf_term pt, ~~ is_exp pt,
                        all wf_term pts, pts != [::] & sorted <=%O pts]
  end.

Lemma wf_exp pt pts :
  wf_term pt ->
  all wf_term pts ->
  wf_term (exp pt pts).
Proof.
rewrite /exp; case: (altP eqP) => //= ptsN0 wf_pt wf_pts.
have ->: wf_term (base pt) by case: pt wf_pt => //= ?? /and5P [].
have ->: ~~ is_exp (base pt) by case: pt wf_pt => //= ?? /and5P [].
rewrite all_sort all_cat wf_pts.
have ->: all wf_term (exps pt) by case: pt wf_pt => //= ?? /and5P [].
rewrite sort_le_sorted andbT -size_eq0 size_sort size_cat addn_eq0 negb_and.
by rewrite ptsN0 orbT.
Qed.

Lemma wf_normalize pt : wf_term (normalize pt).
Proof.
elim: pt => //=.
- by move=> ? -> ? ->.
- by move=> ? -> ? ->.
- move=> pt IHpt pts IHpts; apply: wf_exp => //.
  by elim: pts IHpts {pt IHpt} => //= pt pts IH [-> ?]; rewrite IH.
Qed.

Lemma normalize_wf pt : wf_term pt -> normalize pt = pt.
Proof.
elim: pt => //=.
- by move=> pt1 IH1 pt2 IH2 /andP [??]; rewrite IH1 ?IH2.
- by move=> ?? IH ?; rewrite IH.
- by move=> pt1 IH1 pt2 IH2 /andP [??]; rewrite IH1 ?IH2.
- by move=> ? IH ?; rewrite IH.
- move=> pt IH1 pts IH2 /and5P [wf_pt ptNexp wf_pts ptsN0 sorted_pts].
  rewrite /exp size_map size_eq0 (negbTE ptsN0) IH1 //.
  rewrite base_expN // exps_expN //=.
  suff -> : map normalize pts = pts by rewrite sort_le_id.
  elim: pts {ptsN0 sorted_pts} => //= pt' pts IH in IH2 wf_pts *.
  case: IH2 => IHpt' IHpts.
  case/andP: wf_pts => wf_pt' wf_pts.
  by rewrite IHpt' // IH.
Qed.

Lemma normalize_idem pt : normalize (normalize pt) = normalize pt.
Proof. apply: normalize_wf; exact: wf_normalize. Qed.

Lemma normalize_exp_wf pt pts :
  let pt' := normalize (PTExp pt pts) in
  pts <> [::] ->
  wf_term (PTExp (base pt') (exps pt')).
Proof.
move=> pt' /eqP/negbTE ptsN0.
rewrite (_ : PTExp _ _ = pt') ?wf_normalize //.
by rewrite /pt' /= /exp size_map size_eq0 ptsN0 /=.
Qed.

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
| TExpN' pt pts of PreTerm.wf_term (PreTerm.PTExp pt pts).
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
  | TExpN' pt pts _ => PreTerm.PTExp pt pts
  end.

Fixpoint fold_term_def pt :=
  match pt with
  | PreTerm.PTInt n => TInt n
  | PreTerm.PTPair pt1 pt2 => TPair (fold_term_def pt1) (fold_term_def pt2)
  | PreTerm.PTNonce l => TNonce l
  | PreTerm.PTKey kt pt => TKey kt (fold_term_def pt)
  | PreTerm.PTEnc k pt => TEnc (fold_term_def k) (fold_term_def pt)
  | PreTerm.PTHash pt => THash (fold_term_def pt)
  | PreTerm.PTExp pt' pts' =>
    if pts' =P [::] is ReflectF pts'N0 then
      TExpN' _ _ (PreTerm.normalize_exp_wf pt' pts' pts'N0)
    else fold_term_def pt'
  end.

Lemma wf_unfold_term t : PreTerm.wf_term (unfold_term t).
Proof. by elim/term_ind': t=> //= ? -> ? ->. Qed.

Fact fold_term_key : unit. Proof. exact: tt. Qed.
Definition fold_term :=
  locked_with fold_term_key fold_term_def.
Canonical fold_term_unlockable := [unlockable of fold_term].

Lemma unfold_termK : cancel unfold_term fold_term.
Proof.
rewrite [fold_term]unlock.
elim/term_ind' => //=.
- by move=> t1 IH1 t2 IH2; rewrite IH1 IH2.
- by move=> kt t IH; rewrite IH.
- by move=> t1 IH1 t2 IH2; rewrite IH1 IH2.
- by move=> t IH; rewrite IH.
- move=> pt pts wf.
  have /and5P [wf_pt ptNexp wf_pts ptsN0 sorted_pts] := wf.
  case: eqP ptsN0 => // ptsN0 _.
  move: (PreTerm.normalize_exp_wf _ _ _).
  set pt' := PreTerm.normalize _.
  rewrite -[PreTerm.exp _ _]/pt' /pt' PreTerm.normalize_wf //=.
  move=> ?; apply: congr1; exact: bool_irrelevance.
Qed.

Lemma unfold_fold pt : unfold_term (fold_term pt) = PreTerm.normalize pt.
Proof.
rewrite [fold_term]unlock; elim: pt => //=.
- by move=> ? -> ? ->.
- by move=> ? ? ->.
- by move=> ? -> ? ->.
- by move=> ? ->.
- move=> pt IHpt pts IHpts.
  case: eqP => [->|/eqP ptsN0] //=.
  rewrite PreTerm.base_expsK // PreTerm.is_exp_exp.
  by case: (pts) ptsN0.
Qed.

Lemma fold_termK pt : PreTerm.wf_term pt -> unfold_term (fold_term pt) = pt.
Proof.
by move=> wf; rewrite unfold_fold PreTerm.normalize_wf.
Qed.

Lemma fold_normalize pt : fold_term (PreTerm.normalize pt) = fold_term pt.
Proof. by rewrite -unfold_fold unfold_termK. Qed.

Lemma unfold_term_inj : injective unfold_term.
Proof. exact: can_inj unfold_termK. Qed.

Implicit Types (t k : term) (ts : seq term).

Section TExp.

Fact TExpN_key : unit. Proof. exact: tt. Qed.
Definition TExpN :=
  locked_with TExpN_key (
    fun t ts =>
      fold_term (PreTerm.PTExp (unfold_term t) (map unfold_term ts))
  ).
Canonical TExpN_unlock := [unlockable of TExpN].

End TExp.

Notation TExp t1 t2 := (TExpN t1 [:: t2]).

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

Lemma unfold_TExpN t ts :
  unfold_term (TExpN t ts)
  = PreTerm.exp (unfold_term t) (map unfold_term ts).
Proof.
by rewrite unlock unfold_fold /= normalize_unfold1 normalize_unfoldn.
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
  | PreTerm.PTExp pt pts => TExpN (fold_term pt) (map fold_term pts)
  end.
Proof.
apply/unfold_term_inj. rewrite [fold_term]unlock.
case: pt => //= pt pts; rewrite ?unfold_TExpN.
case: eqP => [->|/eqP ptsN0] //=.
rewrite -unfold_fold unlock -map_comp PreTerm.base_expsK.
- by under [in LHS]eq_map => ? do rewrite -unfold_fold unlock.
- by rewrite PreTerm.is_exp_exp -size_eq0 size_map size_eq0 ptsN0.
Qed.

Definition base t :=
  if t is TExpN' pt _ _ then fold_term pt else t.
Definition exps t :=
  if t is TExpN' _ pts _ then map fold_term pts else [::].

Lemma unfold_base t : unfold_term (base t) = PreTerm.base (unfold_term t).
Proof.
case: t => //= ?? wf; rewrite fold_termK //.
by case/and5P: wf.
Qed.

Lemma unfold_exps t :
  map unfold_term (exps t) = PreTerm.exps (unfold_term t).
Proof.
case: t => //= ?? /and5P [?? /allP wf_ts ??].
rewrite -map_comp map_id_in // => pt /wf_ts pt_in.
by rewrite /= fold_termK.
Qed.

Lemma TExpN_perm t ts1 ts2 : perm_eq ts1 ts2 -> TExpN t ts1 = TExpN t ts2.
Proof.
move=> perm_ts12; apply: unfold_term_inj; rewrite !unfold_TExpN.
apply: PreTerm.perm_exp; exact: perm_map.
Qed.

Lemma TExpNC t ts1 ts2 : TExpN t (ts1 ++ ts2) = TExpN t (ts2 ++ ts1).
Proof. by apply: TExpN_perm; rewrite perm_catC. Qed.

Lemma base_TExpN t ts : base (TExpN t ts) = base t.
Proof.
apply: unfold_term_inj; rewrite !unfold_base unfold_TExpN.
by case: ts=> [|t' ts] //=.
Qed.

Lemma exps_TExpN t ts : exps (TExpN t ts) = sort <=%O (exps t ++ ts).
Proof.
apply: (inj_map unfold_term_inj).
rewrite unfold_exps -sort_map map_cat unfold_exps unfold_TExpN.
rewrite /PreTerm.exp size_map size_eq0.
case: (altP eqP) => [->|tsN0] //=.
rewrite cats0 sort_le_id //.
by case: (unfold_term t) (wf_unfold_term t) => //= ?? /and5P [].
Qed.

Definition is_nonce t :=
  if t is TNonce _ then true else false.

Definition is_exp t :=
  if t is TExpN' _ _ _ then true else false.

Lemma is_exp_unfold t : is_exp t = PreTerm.is_exp (unfold_term t).
Proof. by case: t => //= - []. Qed.

Lemma is_exp_base t : ~~ is_exp (base t).
Proof.
rewrite is_exp_unfold unfold_base.
case: (unfold_term t) (wf_unfold_term t) => //=.
by move=> ? ? /and5P [].
Qed.

Lemma base_expsK t : TExpN (base t) (exps t) = t.
Proof.
apply/unfold_term_inj; rewrite unfold_TExpN unfold_base unfold_exps.
case: (unfold_term t) (wf_unfold_term t) => //=.
move=> pt pts /and5P [_ ptNexp _ ptsN0 sorted_pts].
rewrite /PreTerm.exp size_eq0 (negbTE ptsN0).
rewrite PreTerm.base_expN // PreTerm.exps_expN //=.
by rewrite sort_le_id.
Qed.

Lemma base_exps_inj t1 t2 :
  base t1 = base t2 -> perm_eq (exps t1) (exps t2) -> t1 = t2.
Proof.
move=> eb ee; rewrite -(base_expsK t1) -(base_expsK t2) eb.
exact: TExpN_perm.
Qed.

Lemma base_expN t : ~~ is_exp t -> base t = t.
Proof.
rewrite is_exp_unfold=> tNX; apply: unfold_term_inj.
by rewrite unfold_base PreTerm.base_expN.
Qed.

Lemma exps_expN t : ~~ is_exp t -> exps t = [::].
Proof.
rewrite is_exp_unfold=> tNX; apply: (inj_map unfold_term_inj).
by rewrite unfold_exps PreTerm.exps_expN.
Qed.

Lemma TExpNA t ts1 ts2 : TExpN (TExpN t ts1) ts2 = TExpN t (ts1 ++ ts2).
Proof.
apply: base_exps_inj; rewrite ?base_TExpN // !exps_TExpN.
rewrite !perm_sort perm_sym perm_sort catA perm_cat2r.
by rewrite perm_sym perm_sort.
Qed.

Lemma is_exp_TExpN t ts : is_exp (TExpN t ts) = (ts != [::]) || is_exp t.
Proof. by rewrite !is_exp_unfold unfold_TExpN; case: ts. Qed.

Lemma is_exp_TExp t1 t2 : is_exp (TExp t1 t2).
Proof. by rewrite is_exp_TExpN. Qed.

Lemma TExpN0 t : TExpN t [::] = t.
Proof.
apply: base_exps_inj; rewrite ?base_TExpN //.
by rewrite exps_TExpN cats0 perm_sort.
Qed.

Definition tsize t := PreTerm.tsize (unfold_term t).

Lemma tsize_gt0 t : 0 < tsize t. Proof. exact: PreTerm.tsize_gt0. Qed.

Lemma tsize_TExpN t ts :
  tsize (TExpN t ts)
  = (ts != [::]) && ~~ is_exp t + tsize t + sumn (map tsize ts).
Proof.
rewrite /tsize unfold_TExpN PreTerm.tsize_exp is_exp_unfold.
rewrite -size_eq0 size_map size_eq0.
case: (altP eqP) => [->|tsN0] //=; rewrite ?addn0 //.
rewrite big_cons big_cat /= sumnE !big_map.
case: (boolP (PreTerm.is_exp (unfold_term t))) => [|tNexp] /=.
- case: t => //= pt pts _ _.
  by rewrite big_cons !big_map !addnA add0n addSn.
- by rewrite PreTerm.base_expN // PreTerm.exps_expN //= big_nil add0n.
Qed.

(*
Lemma TExp'E t pts wf : TExp' t pts wf = TExp t (map fold_term pts).
Proof.
apply: unfold_term_inj => /=; rewrite unfold_TExp -[@List.map]/@map.
case/andP: wf => wf_pts sorted_pts.
rewrite -map_comp map_id_in ?sort_le_id // => pt in_pts.
by rewrite /= fold_termK // (allP wf_pts).
Qed.
*)

Lemma TExpN_injl : left_injective TExpN.
Proof.
move=> ts t1 t2 e; apply: base_exps_inj.
- by move/(congr1 base): e; rewrite !base_TExpN.
- move/(congr1 exps): e; rewrite !exps_TExpN.
  by move/perm_sort_leP; rewrite perm_cat2r.
Qed.

Lemma TExpN_injr t ts1 ts2 : TExpN t ts1 = TExpN t ts2 -> perm_eq ts1 ts2.
Proof.
move=> /(congr1 exps); rewrite !exps_TExpN; move/perm_sort_leP.
by rewrite perm_cat2l.
Qed.

Lemma TExp_injr t t1 t2 : TExp t t1 = TExp t t2 -> t1 = t2.
Proof.
by move/TExpN_injr/perm_mem/(_ t2); rewrite !inE eqxx => /eqP.
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
  | TExpN' pt pts _ => PreTerm.tsize (PreTerm.PTExp pt pts)
  end.
Proof. by case: t. Qed.

Lemma tsize_TExpN_lt t1 ts1 t2 :
  (tsize (TExpN t1 ts1) < tsize (TExpN t1 (t2 :: ts1)))%coq_nat /\
  (tsize t2 < tsize (TExpN t1 (t2 :: ts1)))%coq_nat.
Proof.
move/ssrnat.ltP: (tsize_gt0 t1) => pos_t1.
move/ssrnat.ltP: (tsize_gt0 t2) => pos_t2.
rewrite !tsize_TExpN /= -!plusE; case: (altP eqP) => [->|ts1N0] //=; lia.
Qed.

(*
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
*)

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
                   ts != [::] ->
                   sorted <=%O ts ->
        T (TExpN t ts)) :
  forall t, T t.
Proof.
move=> t; rewrite -(unfold_termK t) [fold_term]unlock.
move: (wf_unfold_term t).
elim: (unfold_term t) => {t} /=; do ?by move=> * /=; eauto.
- by move=> t1 IH1 t2 IH2 /andP [/IH1 ? /IH2 ?]; eauto.
- by move=> t1 IH1 t2 IH2 /andP [/IH1 ? /IH2 ?]; eauto.
move=> pt IHpt pts IHpts /and5P [wf_pt ptNexp wf_pts ptsN0 sorted_pts].
case: eqP ptsN0 => //= ptsN0 _.
have [t e_pt] : {t | pt = unfold_term t}.
  by exists (fold_term pt); rewrite fold_termK.
rewrite {}e_pt {pt} in IHpt wf_pt ptNexp *.
have [ts e_pts] : {ts | pts = map unfold_term ts}.
  exists (map fold_term pts).
  rewrite -map_comp map_id_in // => pt' pt'_pts.
  by rewrite /= fold_termK // (allP wf_pts).
move: (PreTerm.normalize_exp_wf _ _ _) => wf.
have tsN0: ts != [::].
  by move/eqP: ptsN0; rewrite e_pts -!size_eq0 size_map.
rewrite {}e_pts {pts ptsN0} in IHpts wf_pts sorted_pts wf *.
rewrite (_ : TExpN' _ _ _ = TExpN t ts); last first.
  apply: unfold_term_inj.
  rewrite unfold_TExpN /PreTerm.exp /= !size_map size_eq0 (negbTE tsN0).
  by rewrite normalize_unfold1 normalize_unfoldn.
apply: H7 => //.
- by rewrite -(unfold_termK t) unlock; apply: IHpt.
- by rewrite is_exp_unfold.
- elim: ts IHpts wf_pts {wf tsN0 sorted_pts} => /= [[] //|t' ts IH [] IHt /IH IHts].
  case/andP => {}/IHt IHt {}/IHts IHts; split => //.
  by rewrite -[t']unfold_termK unlock.
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
