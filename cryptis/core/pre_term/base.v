From cryptis Require Export mathcomp_compat.
From cryptis Require Import mathcomp_utils.
From HB Require Import structures.
From mathcomp Require Import all_order all_boot.
From deriving Require Import deriving.
From Stdlib Require Import ZArith.ZArith Lia.
From iris.heap_lang Require locations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.POrderTheory Order.TotalTheory.

Inductive term_op0 :=
| O0Int of Z
| O0Nonce of locations.loc.

Notation TInt_tag := 0%Z.
Notation TNonce_tag := 1%Z.

Canonical term_op0_indDef := [indDef for term_op0_rect].
Canonical term_op0_indType := IndType term_op0 term_op0_indDef.
Definition term_op0_hasDecEq := [derive hasDecEq for term_op0].
#[warnings="-projection-no-head-constant"]
HB.instance Definition _ := term_op0_hasDecEq.
Definition term_op0_hasChoice := [derive hasChoice for term_op0].
#[warnings="-projection-no-head-constant"]
HB.instance Definition _ := term_op0_hasChoice.
Definition term_op0_isCountable := [derive isCountable for term_op0].
#[warnings="-projection-no-head-constant"]
HB.instance Definition _ := term_op0_isCountable.
Definition term_op0_isOrder := [derive isOrder for term_op0].
HB.instance Definition _ := term_op0_isOrder.

Inductive key_type := AEnc | ADec | Sign | Verify | SEnc.

Canonical key_type_indDef := [indDef for key_type_rect].
Canonical key_type_indType := IndType key_type key_type_indDef.
Definition key_type_hasDecEq := [derive hasDecEq for key_type].
#[warnings="-projection-no-head-constant"]
HB.instance Definition _ := key_type_hasDecEq.
Definition key_type_hasChoice := [derive hasChoice for key_type].
#[warnings="-projection-no-head-constant"]
HB.instance Definition _ := key_type_hasChoice.
Definition key_type_isCountable := [derive isCountable for key_type].
#[warnings="-projection-no-head-constant"]
HB.instance Definition _ := key_type_isCountable.
Definition key_type_isOrder := [derive isOrder for key_type].
HB.instance Definition _ := key_type_isOrder.

Inductive term_op1 :=
| O1Key of key_type
| O1Hash
| O1Inv.

Notation TKey_tag := 0%Z.
Notation THash_tag := 1%Z.
Notation TInv_tag := 2%Z.

Canonical term_op1_indDef := [indDef for term_op1_rect].
Canonical term_op1_indType := IndType term_op1 term_op1_indDef.
Definition term_op1_hasDecEq := [derive hasDecEq for term_op1].
#[warnings="-projection-no-head-constant"]
HB.instance Definition _ := term_op1_hasDecEq.
Definition term_op1_hasChoice := [derive hasChoice for term_op1].
#[warnings="-projection-no-head-constant"]
HB.instance Definition _ := term_op1_hasChoice.
Definition term_op1_isCountable := [derive isCountable for term_op1].
#[warnings="-projection-no-head-constant"]
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
#[warnings="-projection-no-head-constant"]
HB.instance Definition _ := term_op2_hasDecEq.
Definition term_op2_hasChoice := [derive hasChoice for term_op2].
#[warnings="-projection-no-head-constant"]
HB.instance Definition _ := term_op2_hasChoice.
Definition term_op2_isCountable := [derive isCountable for term_op2].
#[warnings="-projection-no-head-constant"]
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
      H6 t (@pre_term_rect' T1 T2 H1 H2 H3 H4 H5 H6 t) ts (loop2 ts)
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
  | O1Inv, O1Inv => true
  | O1Key _, _ => true
  | O1Hash, O1Inv => true
  | _, _ => false
  end.
Proof.
case: o1 o2 => [k1| |] [k2| |] //=.
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

Definition is_nonce pt :=
  if pt is PT0 (O0Nonce _) then true else false.

Definition is_inv pt :=
  if pt is PT1 O1Inv _ then true else false.

Definition is_exp pt :=
  if pt is PTExp _ _ then true else false.

Definition base pt := if pt is PTExp pt _   then pt  else pt.
Definition exps pt := if pt is PTExp pt pts then pts else [::].

Definition inv pt :=
  match pt with
  | PT1 O1Inv t => t
  | _ => PT1 O1Inv pt
  end.

Definition insert_exp pt pts :=
  if inv pt \in pts then rem (inv pt) pts
  else pt :: pts.

Definition cancel_exps := foldr insert_exp [::].

Definition exp pt pts :=
  let canceled := cancel_exps (exps pt ++ pts) in
  if nilp canceled then base pt
  else PTExp (base pt) (sort <=%O canceled).

Fixpoint normalize pt :=
  match pt with
  | PT0 o => PT0 o
  | PT1 o t => match o with
              | O1Inv => inv (normalize t)
              | _ => PT1 o (normalize t)
              end
  | PT2 o t1 t2 => PT2 o (normalize t1) (normalize t2)
  | PTExp t ts => exp (normalize t) (map normalize ts)
  end.

Definition invs_canceled pts := all (fun pt => inv pt \notin pts) pts.

Fixpoint wf_term pt :=
  match pt with
  | PT0 _ => true
  | PT1 O1Inv pt => ~~ is_inv pt && wf_term pt
  | PT1 _ pt => wf_term pt
  | PT2 _ pt1 pt2 => wf_term pt1 && wf_term pt2
  | PTExp pt pts => [&& wf_term pt, ~~ is_exp pt,
                       all wf_term pts, pts != [::],
                       sorted <=%O pts & invs_canceled pts]
  end.

Lemma wf_base pt : wf_term pt -> wf_term (base pt).
Proof. by case: pt => // => ?? /and5P []. Qed.

Lemma wf_exps pt : wf_term pt -> all wf_term (exps pt).
Proof. by case: pt => // => ?? /and5P []. Qed.

Lemma wf_inv pt : wf_term pt -> wf_term (inv pt).
Proof. by case: pt => // - [] ? // /andP []. Qed.

Lemma wf_insert_exp pt pts :
  wf_term pt -> all wf_term pts -> all wf_term (insert_exp pt pts).
Proof.
rewrite /insert_exp => wf wfs. case: ifP => _.
  by apply /allP => ? /mem_rem /(allP wfs).
  by rewrite /= wf.
Qed.

Lemma wf_cancel_exps pts : all wf_term pts -> all wf_term (cancel_exps pts).
Proof. elim: pts => [| ?? IH] // /andP [??]. by rewrite wf_insert_exp // IH. Qed.

Lemma inv_Nid pt : inv pt != pt.
Proof. case: pt => // - [] // ?. apply /eqP => /(f_equal height) /=. lia. Qed.

Lemma eq_Ninv pt1 pt2 : pt1 == pt2 -> pt1 != inv pt2.
Proof. move => /eqP ->. rewrite eq_sym. exact: inv_Nid. Qed.

Lemma inv_involutive pt : wf_term pt -> inv (inv pt) = pt.
Proof. case: pt => // - [] //. by case => // - []. Qed.

Lemma inv_eq_op pt1 pt2 :
  wf_term pt1 -> wf_term pt2 -> (inv pt1 == pt2) = (pt1 == inv pt2).
Proof.
move => wf1 wf2. by apply /(sameP eqP) /(iffP eqP) => [-> | <-]; rewrite inv_involutive.
Qed.

Lemma insert_exp_subseq pt pts : subseq (insert_exp pt pts) (pt :: pts).
Proof.
rewrite /insert_exp. case: ifP => _ //.
by apply: subseq_trans; first apply rem_subseq; last apply subseq_cons.
Qed.

Lemma cancel_exps_subseq pts : subseq (cancel_exps pts) pts.
elim: pts => // [?? IH]; simpl (cancel_exps _).
apply: subseq_trans; first apply insert_exp_subseq; last by simpl; rewrite eqxx.
Qed.

Lemma mem_cancel_exps pts : { subset (cancel_exps pts) <= pts }.
Proof. apply mem_subseq. exact: cancel_exps_subseq. Qed.

Lemma parity_insert_exp pt pts : odd (size (insert_exp pt pts)) = ~~ odd (size pts).
Proof.
rewrite /insert_exp. case: ifP => //.
case: pts => // *. by rewrite size_rem // negbK.
Qed.

Lemma parity_cancel_exps pts : odd (size (cancel_exps pts)) = odd (size pts).
Proof. elim: pts => // [?? IH]. by rewrite parity_insert_exp IH. Qed.

Lemma count_insert_exp pt1 pt2 pts :
  count_mem pt1 (insert_exp pt2 pts) =
  if inv pt2 \in pts then
    count_mem pt1 pts - (pt1 == inv pt2)
  else
    count_mem pt1 pts + (pt1 == pt2).
Proof.
rewrite /insert_exp.
case: ifP => _; rewrite eq_sym.
- exact: count_mem_rem.
- exact: addnC.
Qed.

Lemma count_cancel pt pts :
  wf_term pt -> all wf_term pts ->
  count_mem pt (cancel_exps pts) = count_mem pt pts - count_mem (inv pt) pts.
Proof.
elim: pts => //= [pt' pts' IH] in pt * => ? /andP [??]. rewrite eq_sym.
case: (pt =P pt') => [| /eqP /negbTE]; rewrite count_insert_exp => ->.
- rewrite eqxx eq_sym (negbTE (inv_Nid _)).
  case: ifP => /count_memPn /eqP;
    rewrite !IH ?wf_inv // inv_involutive //.
  + by rewrite -ltnNge => /[dup] /eqP -> /ltnW /eqP ->.
  + rewrite addnC. exact: addnBA.
- rewrite addn0. case: ifP => [_ | /count_memPn /eqP wt0]; rewrite -inv_eq_op // eq_sym.
  + by rewrite IH // subBnAC.
  + move: wt0. case: (pt =P inv pt') => [<- | _ _]; rewrite IH //.
    by rewrite -subBnAC => /eqP ->.
Qed.

Lemma count_perm_cancel pts1 pts2 :
  all wf_term pts1 -> all wf_term pts2 ->
  (forall pt, wf_term pt ->
         count_mem pt pts1 - count_mem (inv pt) pts1 =
         count_mem pt pts2 - count_mem (inv pt) pts2) <->
  perm_eq (cancel_exps pts1) (cancel_exps pts2).
move => wfs1 wfs2. split.
- move => wt_eq. rewrite /perm_eq. apply /allP => /= pt. rewrite mem_cat => /orP pt_in.
  have ?: wf_term pt by case: pt_in => /mem_cancel_exps => [ /(allP wfs1) | /(allP wfs2) ].
  by rewrite !count_cancel // wt_eq.
- move => *. rewrite -!count_cancel //. exact: permP.
Qed.

Lemma count_inv_cancel pt pts :
  wf_term pt -> all wf_term pts ->
  count_mem pt (cancel_exps pts) != 0 -> count_mem (inv pt) (cancel_exps pts) == 0.
Proof.
move => ??. by rewrite !count_cancel ?wf_inv // inv_involutive // -ltnNge => /ltnW.
Qed.

Lemma perm_cancel_exps pts1 pts2 :
  all wf_term pts1 -> perm_eq pts1 pts2 -> perm_eq (cancel_exps pts1) (cancel_exps pts2).
Proof.
move => ? peq. have ?: all wf_term pts2 by rewrite -(perm_all _ peq).
apply count_perm_cancel => // ? _. by rewrite !(permP peq).
Qed.

Lemma base_expN pt : ~~ is_exp pt -> base pt = pt.
Proof. by case: pt. Qed.

Lemma base_Nexp pt : wf_term pt -> ~~ is_exp (base pt).
Proof. by case: pt => // ?? /and5P []. Qed.

Lemma base_idem pt : wf_term pt -> base (base pt) = base pt.
Proof. case pt => //= ?? /and5P [_ ? *]. exact: base_expN. Qed.

Lemma base_exp pt pts : wf_term pt -> base (exp pt pts) = base pt.
Proof. rewrite /exp => ?. case: ifP => //=. by rewrite base_idem. Qed.

Lemma exps_expN pt : ~~ is_exp pt -> exps pt = [::].
Proof. by case: pt. Qed.

Lemma expN_exps pt : wf_term pt -> exps pt = [::] -> ~~ is_exp pt.
Proof. by case: pt => //= [_ ? /and5P [_ _ _ /eqP ?]]. Qed.

Lemma exps_base pt : wf_term pt -> exps (base pt) = [::].
Proof. case: pt => //= ?? /and5P [_ ? *]. exact: exps_expN. Qed.

Lemma exps_exp pt pts :
  wf_term pt ->
  exps (exp pt pts) = sort <=%O (cancel_exps (exps pt ++ pts)).
Proof. move => ?. rewrite /exp. case: (altP nilP) => // ->. by rewrite exps_base. Qed.

Lemma base_expsK pt : is_exp pt -> PTExp (base pt) (exps pt) = pt.
Proof. by case: pt. Qed.

Lemma invs_canceled_exps pt : wf_term pt -> invs_canceled (exps pt).
Proof. by case: pt => //= [pt' pts' /and5P [_ _ _ _ /andP []]]. Qed.

Lemma exps_sorted pt : wf_term pt -> sorted <=%O (exps pt).
Proof. by case: pt => //= [pt' pts' /and5P [_ _ _ _ /andP []]]. Qed.

Lemma inv_invN pt : ~~ is_inv pt -> inv pt = PT1 O1Inv pt.
Proof. by case: pt => - []. Qed.

Lemma perm_exp pt pts1 pts2 :
  wf_term pt -> all wf_term pts1 -> perm_eq pts1 pts2 -> exp pt pts1 = exp pt pts2.
Proof.
move => ???. rewrite /exp /nilp.
have: perm_eq (cancel_exps (exps pt ++ pts1)) (cancel_exps (exps pt ++ pts2)).
  rewrite perm_cancel_exps //.
  - by rewrite all_cat wf_exps.
  - by rewrite perm_cat2l.
by move => /[dup] /perm_sort_leP -> /perm_size ->.
Qed.

Lemma invs_canceled_sort pts : invs_canceled (sort <=%O pts) = invs_canceled pts.
Proof. rewrite /invs_canceled all_sort. apply eq_all => ?. by rewrite mem_sort. Qed.

Lemma invs_canceled_insert_exp pt pts :
  wf_term pt -> all wf_term pts -> invs_canceled pts -> invs_canceled (insert_exp pt pts).
Proof.
move => ? /allP /= wfs /allP /= canceled.
rewrite /invs_canceled. apply /allP. rewrite /insert_exp /= => pt'.
case: ifP => [_| /negP ?].
  - move => /mem_rem /canceled. apply: contraNN. exact: mem_rem.
  - rewrite !inE negb_or. case /orP => [/eqP -> | in_pts].
    + rewrite inv_Nid. exact /negP.
    + apply /andP. split.
      * have ? := wfs _ in_pts.
        apply /eqP => /eqP. rewrite inv_eq_op // => /eqP => eq.
        by rewrite eq in in_pts.
      * exact: canceled.
Qed.

Lemma invs_canceled_cancel_exps pts : all wf_term pts -> invs_canceled (cancel_exps pts).
Proof.
elim: pts => // [?? IH] /andP [??].
apply invs_canceled_insert_exp => //.
  exact: wf_cancel_exps.
  exact: IH.
Qed.

Lemma wf_exp pt pts :
  wf_term pt -> all wf_term pts -> wf_term (exp pt pts).
Proof.
move => ??. rewrite /exp fun_if /= wf_base //.
rewrite /nilp -size_eq0 size_sort.
case: (altP eqP) => //.
rewrite base_Nexp //.
rewrite all_sort wf_cancel_exps ?all_cat ?wf_exps //.
rewrite sort_le_sorted.
by rewrite invs_canceled_sort invs_canceled_cancel_exps ?all_cat ?wf_exps.
Qed.

Lemma wf_normalize pt : wf_term (normalize pt).
Proof.
elim: pt => //= [[] ?? | ?? -> ? -> | ?? ts IHts] //.
  exact: wf_inv.
  apply wf_exp => //. elim: ts IHts => //= [_ ? IHts' [-> ?]]. exact: IHts'.
Qed.

Lemma invs_canceled_cons pt pts : invs_canceled (pt :: pts) -> invs_canceled pts.
Proof.
rewrite /invs_canceled /= => /andP [_ /allP canceled].
apply /allP => t t_in.
have x: inv t \notin pt :: pts. exact: canceled.
apply: contraNN x => in_pts. by rewrite in_cons in_pts orbT.
Qed.

Lemma insert_exp_canceled pt pts :
  invs_canceled (pt :: pts) -> insert_exp pt pts = pt :: pts.
Proof.
rewrite /insert_exp => /allP canceled.
have x: inv pt \notin pt :: pts. apply /canceled /mem_head.
have /negbTE -> : inv pt \notin pts. apply: contraNN x => in_pts. by rewrite in_cons in_pts orbT.
reflexivity.
Qed.

Lemma cancel_exps_canceled pts :
  invs_canceled pts -> cancel_exps pts = pts.
Proof.
elim: pts => // [?? IH] canceled /=.
rewrite insert_exp_canceled //; rewrite IH //; exact: (invs_canceled_cons canceled).
Qed.

Lemma cancel_exps_exps pt :
  wf_term pt -> cancel_exps (exps pt) = exps pt.
Proof. move => ?. apply cancel_exps_canceled. exact: invs_canceled_exps. Qed.

Lemma exp_nil pt : wf_term pt -> exp pt [::] = pt.
Proof.
move => wf.
rewrite /exp cats0 cancel_exps_exps // sort_le_id ?exps_sorted //.
case: pt wf => //= [?? /and5P [_ _ _]]. by rewrite nilpE => /negbTE ->.
Qed.

Lemma is_exp_exp pt pts :
  wf_term pt -> ~~ is_exp pt -> invs_canceled pts ->
  is_exp (exp pt pts) = (pts != [::]).
Proof.
move => ?. case: pts => //=.
  by rewrite exp_nil // => /negbTE.
  move => *. by rewrite /exp exps_expN // cancel_exps_canceled.
Qed.

Lemma normalize_wf pt : wf_term pt -> normalize pt = pt.
Proof.
elim: pt => //.
- move => [[] ? IH ? | ? IH ? | ? IH /andP [??]] /=; rewrite ?IH //. exact: inv_invN.
- by move => /= ?? IH1 ? IH2 /andP [/IH1 -> /IH2 ->].
- move => ? IH ts IHts /and5P [?? wf_ts /negbTE tsN0 /andP [??]] /=.
  have -> : map normalize ts = ts.
    elim: (ts) IHts wf_ts => // [t' ts' IHts' [IHt' ?] /andP [??]] /=.
    by rewrite IHt' // IHts'.
  by rewrite IH // /exp exps_expN // cancel_exps_canceled // nilpE tsN0 base_expN // sort_le_id.
Qed.

Lemma normalize_idem pt : normalize (normalize pt) = normalize pt.
Proof. apply: normalize_wf; exact: wf_normalize. Qed.

Lemma normalize_exp_wf pt pts :
  let pt' := normalize (PTExp pt pts) in
  exps pt' <> [::] ->
  wf_term (PTExp (base pt') (exps pt')).
Proof.
move => pt' /eqP expsN0. rewrite base_expsK ?wf_normalize //.
by apply: contraNT expsN0 => /exps_expN ->.
Qed.

Lemma tsize_inv pt : ~~ is_inv pt -> tsize (inv pt) = S (tsize pt).
Proof. move => ?. by rewrite inv_invN. Qed.

Lemma tsize_exp t ts :
  ~~is_exp t -> invs_canceled ts ->
  tsize (exp t ts) =
  if ts == [::] then tsize t
  else S (\sum_(t' <- base t :: ts) tsize t').
Proof.
move => ??.
rewrite /exp [LHS]fun_if.
rewrite base_expN //.
rewrite exps_expN // cancel_exps_canceled //=.
have e: perm_eq (sort <=%O ts) ts by rewrite perm_sort.
rewrite nilpE.
by rewrite !big_cons !big_map (perm_big _ e).
Qed.

Module Exports.
HB.reexport.
End Exports.

End PreTerm.

Export PreTerm.Exports.
