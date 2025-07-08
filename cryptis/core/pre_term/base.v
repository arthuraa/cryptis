From cryptis Require Export mathcomp_compat.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From deriving Require Import deriving.
From Stdlib Require Import ZArith.ZArith Lia.
From iris.heap_lang Require locations.

Import Order.POrderTheory Order.TotalTheory.

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

Notation TInt_tag := 0%Z.
Notation TPair_tag := 1%Z.
Notation TNonce_tag := 2%Z.
Notation TKey_tag := 3%Z.
Notation TSeal_tag := 4%Z.
Notation THash_tag := 5%Z.
Notation TExp_tag := 6%Z.

Module PreTerm.

Unset Elimination Schemes.
Inductive pre_term :=
| PTInt of Z
| PTPair of pre_term & pre_term
| PTNonce of locations.loc
| PTKey of key_type & pre_term
| PTSeal of pre_term & pre_term
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
  (H5 : forall t1, T1 t1 -> forall t2, T1 t2 -> T1 (PTSeal t1 t2))
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
    | PTSeal t1 t2 => H5 t1 (loop1 t1) t2 (loop1 t2)
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
  (H5 : forall t1, T1 t1 -> forall t2, T1 t2 -> T1 (PTSeal t1 t2))
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
Definition pre_term_hasDecEq := [derive hasDecEq for pre_term].
#[export] HB.instance Definition _ := pre_term_hasDecEq.
Definition pre_term_hasChoice := [derive hasChoice for pre_term].
#[export] HB.instance Definition _ := pre_term_hasChoice.
Definition pre_term_isCountable := [derive isCountable for pre_term].
#[export] HB.instance Definition _ := pre_term_isCountable.
Definition pre_term_isOrder := [derive isOrder for pre_term].
#[export] HB.instance Definition _ := pre_term_isOrder.

Definition pre_term_rect (T : pre_term -> Type)
  (H1 : forall n, T (PTInt n))
  (H2 : forall t1, T t1 -> forall t2, T t2 -> T (PTPair t1 t2))
  (H3 : forall l, T (PTNonce l))
  (H4 : forall kt t, T t -> T (PTKey kt t))
  (H5 : forall t1, T t1 -> forall t2, T t2 -> T (PTSeal t1 t2))
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
Definition seq_pre_term_isOrder := [derive isOrder for seq pre_term].
HB.instance Definition _ := seq_pre_term_isOrder.

Definition cons_num pt : Z :=
  match pt with
  | PTInt _ => TInt_tag
  | PTPair _ _ => TPair_tag
  | PTNonce _ => TNonce_tag
  | PTKey _ _ => TKey_tag
  | PTSeal _ _ => TSeal_tag
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
    | PTSeal k1 pt1, PTSeal k2 pt2 =>
      if k1 == k2 then (pt1 <= pt2)%O
      else (k1 <= k2)%O
    | PTHash pt1, PTHash pt2 => (pt1 <= pt2)%O
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
    => [n1|pt11 pt12|a1|kt1 pt1|pt11 pt12|pt1|pt1 pts1]
       [n2|pt21 pt22|a2|kt2 pt2|pt21 pt22|pt2|pt2 pts2] //=.
- by rewrite [RHS]le_alt.
- by rewrite [(pt12 <= pt22)%O]le_alt.
- by rewrite [RHS]le_alt.
- by rewrite (le_alt _ _ pt1).
- by rewrite (le_alt _ _ pt12).
- by rewrite (le_alt _ _ pt1).
have -> : ((pts1 : seqlexi_with Order.default_display _) <= pts2)%O =
          ((pts1 : seq_pre_term) <= pts2)%O.
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
  | PTSeal k t => S (maxn (height k) (height t))
  | PTHash t => S (height t)
  | PTExp t ts => S (\max_(x <- height t :: map height ts) x)
  end.

Fixpoint tsize pt :=
  match pt with
  | PTInt _ => 1
  | PTPair pt1 pt2 => S (tsize pt1 + tsize pt2)
  | PTNonce _ => 1
  | PTKey _ t => S (tsize t)
  | PTSeal k t => S (S (tsize k) + tsize t)
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

Definition is_nonce pt :=
  if pt is PTNonce _ then true else false.

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
  | PTSeal k t => PTSeal (normalize k) (normalize t)
  | PTHash t => PTHash (normalize t)
  | PTExp t ts => exp (normalize t) (map normalize ts)
  end.

Fixpoint wf_term pt :=
  match pt with
  | PTInt _ => true
  | PTPair pt1 pt2 => wf_term pt1 && wf_term pt2
  | PTNonce _ => true
  | PTKey _ pt => wf_term pt
  | PTSeal k pt => wf_term k && wf_term pt
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

Module Exports.
HB.reexport.
End Exports.

End PreTerm.

Export PreTerm.Exports.
