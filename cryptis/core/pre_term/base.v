From cryptis Require Export mathcomp_compat.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From deriving Require Import deriving.
From Stdlib Require Import ZArith.ZArith Lia.
From iris.heap_lang Require locations.

Import Order.POrderTheory Order.TotalTheory.

Inductive term_op0 :=
| O0Int of Z
| O0Nonce of locations.loc.

Notation TInt_tag := 0%Z.
Notation TNonce_tag := 1%Z.

Canonical term_op0_indDef := [indDef for term_op0_rect].
Canonical term_op0_indType := IndType term_op0 term_op0_indDef.
Definition term_op0_hasDecEq := [derive hasDecEq for term_op0].
HB.instance Definition _ := term_op0_hasDecEq.
Definition term_op0_hasChoice := [derive hasChoice for term_op0].
HB.instance Definition _ := term_op0_hasChoice.
Definition term_op0_isCountable := [derive isCountable for term_op0].
HB.instance Definition _ := term_op0_isCountable.
Definition term_op0_isOrder := [derive isOrder for term_op0].
HB.instance Definition _ := term_op0_isOrder.

Inductive key_type := AEnc | ADec | Sign | Verify | SEnc.

Canonical key_type_indDef := [indDef for key_type_rect].
Canonical key_type_indType := IndType key_type key_type_indDef.
Definition key_type_hasDecEq := [derive hasDecEq for key_type].
HB.instance Definition _ := key_type_hasDecEq.
Definition key_type_hasChoice := [derive hasChoice for key_type].
HB.instance Definition _ := key_type_hasChoice.
Definition key_type_isCountable := [derive isCountable for key_type].
HB.instance Definition _ := key_type_isCountable.
Definition key_type_isOrder := [derive isOrder for key_type].
HB.instance Definition _ := key_type_isOrder.

Inductive term_op1 :=
| O1Key of key_type
| O1Hash.

Notation TKey_tag := 0%Z.
Notation THash_tag := 1%Z.

Canonical term_op1_indDef := [indDef for term_op1_rect].
Canonical term_op1_indType := IndType term_op1 term_op1_indDef.
Definition term_op1_hasDecEq := [derive hasDecEq for term_op1].
HB.instance Definition _ := term_op1_hasDecEq.
Definition term_op1_hasChoice := [derive hasChoice for term_op1].
HB.instance Definition _ := term_op1_hasChoice.
Definition term_op1_isCountable := [derive isCountable for term_op1].
HB.instance Definition _ := term_op1_isCountable.
Definition term_op1_isOrder := [derive isOrder for term_op1].
HB.instance Definition _ := term_op1_isOrder.

Inductive term_op2 :=
| O2Pair
| O2Seal.

Notation TPair_tag := 0%Z.
Notation TSeal_tag := 1%Z.

Canonical term_op2_indDef := [indDef for term_op2_rect].
Canonical term_op2_indType := IndType term_op2 term_op2_indDef.
Definition term_op2_hasDecEq := [derive hasDecEq for term_op2].
HB.instance Definition _ := term_op2_hasDecEq.
Definition term_op2_hasChoice := [derive hasChoice for term_op2].
HB.instance Definition _ := term_op2_hasChoice.
Definition term_op2_isCountable := [derive isCountable for term_op2].
HB.instance Definition _ := term_op2_isCountable.
Definition term_op2_isOrder := [derive isOrder for term_op2].
HB.instance Definition _ := term_op2_isOrder.

Notation TOp0_tag := 0%Z.
Notation TOp1_tag := 1%Z.
Notation TOp2_tag := 2%Z.
Notation TExp_tag := 3%Z.

Module PreTerm.

Unset Elimination Schemes.
Inductive pre_term :=
| PT0 of term_op0
| PT1 of term_op1 & pre_term
| PT2 of term_op2 & pre_term & pre_term
| PTExp of pre_term & list pre_term.
Set Elimination Schemes.

Definition pre_term_rect'
  (T1 : pre_term -> Type)
  (T2 : list pre_term -> Type)
  (H1 : forall o, T1 (PT0 o))
  (H2 : forall o t1, T1 t1 -> T1 (PT1 o t1))
  (H3 : forall o t1, T1 t1 -> forall t2, T1 t2 -> T1 (PT2 o t1 t2))
  (H4 : forall t, T1 t -> forall ts, T2 ts -> T1 (PTExp t ts))
  (H5 : T2 [::])
  (H6 : forall t, T1 t -> forall ts, T2 ts -> T2 (t :: ts)) :=
  fix loop1 t {struct t} : T1 t :=
    match t with
    | PT0 o => H1 o
    | PT1 o t => H2 o t (loop1 t)
    | PT2 o t1 t2 => H3 o t1 (loop1 t1) t2 (loop1 t2)
    | PTExp t ts =>
      let fix loop2 ts {struct ts} : T2 ts :=
          match ts with
          | [::] => H5
          | t :: ts => H6 t (loop1 t) ts (loop2 ts)
          end in
      H4 t (loop1 t) ts (loop2 ts)
    end.

Definition list_pre_term_rect'
  (T1 : pre_term -> Type)
  (T2 : list pre_term -> Type)
  (H1 : forall o, T1 (PT0 o))
  (H2 : forall o t1, T1 t1 -> T1 (PT1 o t1))
  (H3 : forall o t1, T1 t1 -> forall t2, T1 t2 -> T1 (PT2 o t1 t2))
  (H4 : forall t, T1 t -> forall ts, T2 ts -> T1 (PTExp t ts))
  (H5 : T2 [::])
  (H6 : forall t, T1 t -> forall ts, T2 ts -> T2 (t :: ts)) :=
  fix loop2 ts {struct ts} : T2 ts :=
    match ts with
    | [::] => H5
    | t :: ts =>
      H6 t (pre_term_rect' T1 T2 H1 H2 H3 H4 H5 H6 t) ts (loop2 ts)
    end.

Combined Scheme pre_term_list_pre_term_rect
  from pre_term_rect', list_pre_term_rect'.

Definition pre_term_list_pre_term_indDef :=
  [indDef for pre_term_list_pre_term_rect].
Canonical pre_term_indType := IndType pre_term pre_term_list_pre_term_indDef.
Definition pre_term_hasDecEq := [derive hasDecEq for pre_term].
#[export] HB.instance Definition _ := pre_term_hasDecEq.
Definition pre_term_hasChoice := [derive hasChoice for pre_term].
#[export] HB.instance Definition _ := pre_term_hasChoice.
Definition pre_term_isCountable := [derive isCountable for pre_term].
#[export] HB.instance Definition _ := pre_term_isCountable.
Definition pre_term_isOrder := [derive isOrder for pre_term].
#[export] HB.instance Definition _ := pre_term_isOrder.

Definition pre_term_rect (T : pre_term -> Type)
  (H1 : forall o, T (PT0 o))
  (H2 : forall o t1, T t1 -> T (PT1 o t1))
  (H3 : forall o t1, T t1 -> forall t2, T t2 -> T (PT2 o t1 t2))
  (H4 : forall t, T t ->
        forall ts, foldr (fun t R => T t * R)%type unit ts ->
          T (PTExp t ts)) t : T t.
Proof.
exact: (@pre_term_rect' T (foldr (fun t R => T t * R)%type unit)).
Defined.

Definition pre_term_ind (T : pre_term -> Prop) :=
  @pre_term_rect T.

Definition seq_pre_term := seq pre_term.
Definition seq_pre_term_isOrder := [derive isOrder for seq pre_term].
HB.instance Definition _ := seq_pre_term_isOrder.

Definition cons_num pt : Z :=
  match pt with
  | PT0 _ => TOp0_tag
  | PT1 _ _ => TOp1_tag
  | PT2 _ _ _ => TOp2_tag
  | PTExp _ _ => TExp_tag
  end.

Open Scope order_scope.

Lemma le_alt d (T : orderType d) (x y : T) :
  (x <= y)%O = if x == y then true else (x <= y)%O.
Proof. by case: (ltgtP x y). Qed.

Lemma op0_leqE (o1 o2 : term_op0) :
  (o1 <= o2)%O =
  match o1, o2 with
  | O0Int n1, O0Int n2 => (n1 <= n2)%O
  | O0Nonce a1, O0Nonce a2 => (a1 <= a2)%O
  | O0Int _, _ => true
  | O0Nonce _, _ => false
  end.
Proof.
case: o1 o2 => [n1|a1] [n2|a2] //=.
- by rewrite [RHS]le_alt.
- by rewrite [RHS]le_alt.
Qed.

Lemma op1_leqE (o1 o2 : term_op1) :
  (o1 <= o2)%O =
  match o1, o2 with
  | O1Key k1, O1Key k2 => (k1 <= k2)%O
  | O1Hash, O1Hash => true
  | O1Key _, _ => true
  | _, _ => false
  end.
Proof.
case: o1 o2 => [k1|] [k2|] //=.
by rewrite [RHS]le_alt.
Qed.

Lemma leqE pt1 pt2 :
  (pt1 <= pt2)%O =
  if cons_num pt1 == cons_num pt2 then
    match pt1, pt2 with
    | PT0 o1, PT0 o2 => (o1 <= o2)%O
    | PT1 o1 t1, PT1 o2 t2 =>
      if o1 == o2 then (t1 <= t2)%O else (o1 <= o2)%O
    | PT2 o1 t11 t12, PT2 o2 t21 t22 =>
      if o1 == o2 then
        if t11 == t21 then (t12 <= t22)%O else (t11 <= t21)%O
      else (o1 <= o2)%O
    | PTExp pt1 pts1, PTExp pt2 pts2 =>
      if pt1 == pt2 then ((pts1 : seqlexi_with Order.default_display _) <= pts2)%O
      else (pt1 <= pt2)%O
    | _, _ => false
    end
  else (cons_num pt1 <=? cons_num pt2)%Z.
Proof.
have le_alt (T : orderType _) (x y : T) :
    (x <= y)%O = if x == y then true else (x <= y)%O.
  by case: (ltgtP x y).
case: pt1 pt2
    => [o1|o1 t1|o1 t11 t12|t1 ts1]
       [o2|o2 t2|o2 t21 t22|t2 ts2] //=.
- by rewrite [RHS]le_alt.
- by rewrite [(t1 <= t2)%O]le_alt.
- by rewrite (le_alt _ _ t12).
have -> : ((ts1 : seqlexi_with Order.default_display _) <= ts2)%O =
          ((ts1 : seq_pre_term) <= ts2)%O.
  elim: ts1 ts2 {t1 t2} => [|t1 ts1 IH] [|t2 ts2] //=.
  rewrite [LHS](_ : _ = if t1 == t2 then if ts1 == ts2 then true
                                         else ((ts1 : seq_pre_term) <= ts2)%O
                        else (t1 <= t2)%O) //.
  rewrite lexi_cons IH.
  case: ltgtP => //= _; exact: le_alt.
by rewrite [(ts1 : seq_pre_term)  <= ts2]le_alt.
Qed.

Close Scope order_scope.

Fixpoint height pt :=
  match pt with
  | PT0 _ => 1
  | PT1 _ pt => S (height pt)
  | PT2 _ pt1 pt2 => S (maxn (height pt1) (height pt2))
  | PTExp t ts => S (\max_(x <- height t :: map height ts) x)
  end.

Fixpoint tsize pt :=
  match pt with
  | PT0 _ => 1
  | PT1 _ pt => S (tsize pt)
  | PT2 _ t1 t2 => S (tsize t1 + tsize t2)
  | PTExp t ts => S (\sum_(x <- tsize t :: map tsize ts) x)
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

Definition is_nonce pt :=
  if pt is PT0 (O0Nonce _) then true else false.

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
  | PT0 o => PT0 o
  | PT1 o t => PT1 o (normalize t)
  | PT2 o t1 t2 => PT2 o (normalize t1) (normalize t2)
  | PTExp t ts => exp (normalize t) (map normalize ts)
  end.

Fixpoint wf_term pt :=
  match pt with
  | PT0 _ => true
  | PT1 _ pt => wf_term pt
  | PT2 _ pt1 pt2 => wf_term pt1 && wf_term pt2
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
- by move=> _ ? -> ? ->.
- move=> pt IHpt pts IHpts; apply: wf_exp => //.
  by elim: pts IHpts {pt IHpt} => //= pt pts IH [-> ?]; rewrite IH.
Qed.

Lemma normalize_wf pt : wf_term pt -> normalize pt = pt.
Proof.
elim: pt => //=.
- by move=> ?? IH ?; rewrite IH.
- by move=> ? pt1 IH1 pt2 IH2 /andP [??]; rewrite IH1 ?IH2.
move=> pt IH1 pts IH2 /and5P [wf_pt ptNexp wf_pts ptsN0 sorted_pts].
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

Module Exports.
HB.reexport.
End Exports.

End PreTerm.

Export PreTerm.Exports.
