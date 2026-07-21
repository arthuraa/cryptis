From cryptis Require Export mathcomp_compat.
From HB Require Import structures.
From mathcomp Require Import all_order all_boot.
From deriving Require Import deriving.
From Stdlib Require Import ZArith.ZArith Lia.
From iris.heap_lang Require locations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.POrderTheory Order.TotalTheory.

(* A nonce is a nominal wrapper around a heap location.  It coerces back to its
   location, so the meta / freshness machinery (all keyed on [loc]) is unchanged. *)
Record nonce := Nonce { nonce_loc : locations.loc }.

#[warnings="-projection-no-head-constant"]
HB.instance Definition _ := [isNew for nonce_loc].
HB.instance Definition _ := [Equality of nonce by <:].
HB.instance Definition _ := [Choice of nonce by <:].
HB.instance Definition _ := [Countable of nonce by <:].
HB.instance Definition _ := [Order of nonce by <:].

Inductive term_op0 :=
| O0Int of Z
| O0Nonce of nonce.

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
| O2Seal
| O2Exp.

Notation TPair_tag := 0%Z.
Notation TSeal_tag := 1%Z.
Notation TExp_tag := 2%Z.

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
Notation TMul_tag := 3%Z.

Module PreTerm.

Unset Elimination Schemes.
Inductive pre_term :=
| PT0 of term_op0
| PT1 of term_op1 & pre_term
| PT2 of term_op2 & pre_term & pre_term
| PTMul of list pre_term.
Set Elimination Schemes.

(** Convenient shorthands for some operations *)
Notation PTInv e := (PT1 O1Inv e).
Notation PTExp b e := (PT2 O2Exp b e).

Definition pre_term_rect'
  (T1 : pre_term -> Type)
  (T2 : list pre_term -> Type)
  (H1 : forall o, T1 (PT0 o))
  (H2 : forall o t1, T1 t1 -> T1 (PT1 o t1))
  (H3 : forall o t1, T1 t1 -> forall t2, T1 t2 -> T1 (PT2 o t1 t2))
  (Hmul : forall ts, T2 ts -> T1 (PTMul ts))
  (H5 : T2 [::])
  (H6 : forall t, T1 t -> forall ts, T2 ts -> T2 (t :: ts)) :=
  fix loop1 t {struct t} : T1 t :=
    match t with
    | PT0 o => H1 o
    | PT1 o t => H2 o t (loop1 t)
    | PT2 o t1 t2 => H3 o t1 (loop1 t1) t2 (loop1 t2)
    | PTMul ts =>
      let fix loop2 ts {struct ts} : T2 ts :=
          match ts with
          | [::] => H5
          | t :: ts => H6 t (loop1 t) ts (loop2 ts)
          end in
      Hmul ts (loop2 ts)
    end.

Definition list_pre_term_rect'
  (T1 : pre_term -> Type)
  (T2 : list pre_term -> Type)
  (H1 : forall o, T1 (PT0 o))
  (H2 : forall o t1, T1 t1 -> T1 (PT1 o t1))
  (H3 : forall o t1, T1 t1 -> forall t2, T1 t2 -> T1 (PT2 o t1 t2))
  (Hmul : forall ts, T2 ts -> T1 (PTMul ts))
  (H5 : T2 [::])
  (H6 : forall t, T1 t -> forall ts, T2 ts -> T2 (t :: ts)) :=
  fix loop2 ts {struct ts} : T2 ts :=
    match ts with
    | [::] => H5
    | t :: ts =>
      H6 t (@pre_term_rect' T1 T2 H1 H2 H3 Hmul H5 H6 t) ts (loop2 ts)
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
  (Hmul : forall ts, foldr (fun t R => T t * R)%type unit ts ->
          T (PTMul ts)) t : T t.
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
  | PTMul _ => TMul_tag
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
    | PTMul ts1, PTMul ts2 =>
      ((ts1 : seqlexi_with Order.default_display _) <= ts2)%O
    | _, _ => false
    end
  else (cons_num pt1 <=? cons_num pt2)%Z.
Proof.
have le_alt (T : orderType _) (x y : T) :
    (x <= y)%O = if x == y then true else (x <= y)%O.
  by case: (ltgtP x y).
case: pt1 pt2
    => [o1|o1 t1|o1 t11 t12|ts1]
       [o2|o2 t2|o2 t21 t22|ts2] //=.
- by rewrite [RHS]le_alt.
- by rewrite [(t1 <= t2)%O]le_alt.
- by rewrite (le_alt _ _ t12).
have -> : ((ts1 : seqlexi_with Order.default_display _) <= ts2)%O =
          ((ts1 : seq_pre_term) <= ts2)%O.
  elim: ts1 ts2 => [|t1 ts1 IH] [|t2 ts2] //=.
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
  | PTMul ts => S (\max_(x <- map height ts) x)
  end.

Fixpoint tsize pt :=
  match pt with
  | PT0 _ => 1
  | PT1 _ pt => S (tsize pt)
  | PT2 _ t1 t2 => S (tsize t1 + tsize t2)
  | PTMul ts => S (\sum_(x <- map tsize ts) x)
  end.

Lemma tsize_gt0 pt : 0 < tsize pt. Proof. by case: pt. Qed.

Definition is_nonce pt :=
  if pt is PT0 (O0Nonce _) then true else false.

Definition is_inv pt :=
  if pt is PTInv _ then true else false.

Definition is_exp pt :=
  if pt is PTExp _ _ then true else false.

Definition is_mul pt :=
  if pt is PTMul _ then true else false.

Definition base pt := if pt is PTExp b _ then b else pt.
Definition expo pt := if pt is PTExp _ e then e else PTMul [::].
Definition factors pt := if pt is PTMul ts then ts else [:: pt].
Definition exps pt := factors (expo pt).

(** We now define smart constructors for all the operations that validate
    non-trivial equations: [inv], [mul] and [exp].  The definitions work as
    follows:

    - [inv_aux] computes the inverse of terms that do not begin with [PTMul] by
      simply adding or removing a [PTInv].

    - [mul] computes the product of a list of terms. It flattens inner terms
      that begin with [PTMul] (so that multiplication is associative) and then
      cancels out multiplicative inverses by using [inv_aux].  This works
      because, on normalized terms, consecutive occurrences of [PTMul] are
      flattened, so [inv_aux] is only called on non-multiplication terms.

    - [inv] computes the inverse of arbitrary terms by distributivity: [inv (a1
      * ... * an) = inv_aux a1 * ... inv_aux an].  Once again, this works
      because, on normalized terms, the [ai] do not begin with [PTMul].

    - [exp] combines exponents using [mul].  If the resulting exponent is [1 =
      PTMul []], we simply return the base. *)

Definition inv_aux pt :=
  match pt with
  | PTInv t => t
  | _ => PTInv pt
  end.

Definition insert_factor pt pts :=
  if inv_aux pt \in pts then rem (inv_aux pt) pts
  else pt :: pts.

Definition cancel_invs := foldr insert_factor [::].

Definition mul ts :=
  match sort <=%O (cancel_invs (flatten (map factors ts))) with
  | [:: t] => t
  | canceled => PTMul canceled
  end.

Definition inv pt :=
  if pt is PTMul ts then mul (map inv_aux ts) else inv_aux pt.

Definition exp b e :=
  let e' := mul [:: expo b; e] in
  if e' == PTMul [::] then base b
  else PTExp (base b) e'.

Fixpoint normalize pt :=
  match pt with
  | PT0 o => PT0 o
  | PTInv t => inv (normalize t)
  | PT1 o t => PT1 o (normalize t)
  | PTExp b e => exp (normalize b) (normalize e)
  | PT2 o t1 t2 => PT2 o (normalize t1) (normalize t2)
  | PTMul ts => mul (map normalize ts)
  end.

(** [invs_canceled pts] holds when all the inverses in [pts] have been canceled
    out. *)
Definition invs_canceled pts := all (fun pt => inv pt \notin pts) pts.

Fixpoint wf_term pt :=
  match pt with
  | PT0 _ => true
  | PTInv pt => [&& ~~ is_inv pt, ~~ is_mul pt & wf_term pt]
  | PT1 _ pt => wf_term pt
  | PTExp b e => [&& wf_term b, ~~ is_exp b, wf_term e & e != PTMul [::]]
  | PT2 _ pt1 pt2 => wf_term pt1 && wf_term pt2
  | PTMul ts => [&& all wf_term ts, all (fun t => ~~ is_mul t) ts,
                    sorted <=%O ts, invs_canceled ts & size ts != 1]
  end.

Lemma wf_base pt : wf_term pt -> wf_term (base pt).
Proof. by case: pt => [o|o t|[||] t1 t2|ts] //= /and4P []. Qed.

Lemma base_expN pt : ~~ is_exp pt -> base pt = pt.
Proof. by case: pt => [o|o t|[||] t1 t2|ts]. Qed.

Lemma base_Nexp pt : wf_term pt -> ~~ is_exp (base pt).
Proof. by case: pt => [o|o t|[||] t1 t2|ts] //= /and4P []. Qed.

Lemma base_idem pt : wf_term pt -> base (base pt) = base pt.
Proof. by move => wf; rewrite base_expN // base_Nexp. Qed.

Lemma expo_expN pt : ~~ is_exp pt -> expo pt = PTMul [::].
Proof. by case: pt => [o|o t|[||] t1 t2|ts]. Qed.

Lemma wf_expo pt : wf_term pt -> wf_term (expo pt).
Proof. by case: pt => [o|o t|[||] t1 t2|ts] //= /and4P []. Qed.

Lemma factorsN pt : ~~ is_mul pt -> factors pt = [:: pt].
Proof. by case: pt. Qed.

Lemma wf_factors pt : wf_term pt -> all wf_term (factors pt).
Proof.
case: pt => [o|o t|o t1 t2|ts] wf //=; rewrite ?andbT //.
by case/and5P: wf.
Qed.

Lemma Nmul_factors pt : wf_term pt -> all (fun t => ~~ is_mul t) (factors pt).
Proof.
case: pt => [o|o t|o t1 t2|ts] wf //=; rewrite ?andbT //.
by case/and5P: wf.
Qed.

Lemma wf_exps pt : wf_term pt -> all wf_term (exps pt).
Proof. by move => wf; rewrite /exps; apply: wf_factors; apply: wf_expo. Qed.

Lemma wf_inv_aux pt : wf_term pt -> ~~ is_mul pt -> wf_term (inv_aux pt).
Proof. by case: pt => [o|[k| |] t|o t1 t2|ts] //= /and3P []. Qed.

Lemma is_mul_inv_aux pt : wf_term pt -> ~~ is_mul (inv_aux pt).
Proof. by case: pt => [o|[k| |] t|o t1 t2|ts] //= /and3P []. Qed.

Lemma inv_aux_Nid pt : inv_aux pt != pt.
Proof. case: pt => // - [] // ?. apply /eqP => /(congr1 height) /=. lia. Qed.

Lemma inv_auxK pt : wf_term pt -> inv_aux (inv_aux pt) = pt.
Proof. by case: pt => // - [] // [] // []. Qed.

Lemma inv_aux_eq_op pt1 pt2 :
  wf_term pt1 -> wf_term pt2 -> (inv_aux pt1 == pt2) = (pt1 == inv_aux pt2).
Proof. move => ??; by apply /(sameP eqP) /(iffP eqP) => [-> | <-]; rewrite inv_auxK. Qed.

Lemma insert_factor_subseq pt pts : subseq (insert_factor pt pts) (pt :: pts).
Proof.
rewrite /insert_factor. case: ifP => _ //.
by apply: subseq_trans; [apply rem_subseq | apply subseq_cons].
Qed.

Lemma cancel_invs_subseq pts : subseq (cancel_invs pts) pts.
elim: pts => // [?? IH]; simpl (cancel_invs _).
apply: subseq_trans; first apply insert_factor_subseq; last by simpl; rewrite eqxx.
Qed.

Lemma mem_cancel_invs pts : { subset (cancel_invs pts) <= pts }.
Proof. apply mem_subseq. exact: cancel_invs_subseq. Qed.

Lemma wf_cancel_invs pts : all wf_term pts -> all wf_term (cancel_invs pts).
Proof. move => /allP H. apply /allP => ? /mem_cancel_invs. exact: H. Qed.

Lemma Nmul_cancel_invs pts :
  all (fun t => ~~ is_mul t) pts -> all (fun t => ~~ is_mul t) (cancel_invs pts).
Proof. move => /allP H. apply /allP => ? /mem_cancel_invs. exact: H. Qed.

Lemma parity_insert_factor pt pts : odd (size (insert_factor pt pts)) = ~~ odd (size pts).
Proof.
rewrite /insert_factor. case: ifP => //.
case: pts => // *. by rewrite size_rem // negbK.
Qed.

Lemma parity_cancel_invs pts : odd (size (cancel_invs pts)) = odd (size pts).
Proof. elim: pts => // [?? IH]. by rewrite parity_insert_factor IH. Qed.

Lemma count_insert_factor pt1 pt2 pts :
  count_mem pt1 (insert_factor pt2 pts) =
  if inv_aux pt2 \in pts then
    count_mem pt1 pts - (pt1 == inv_aux pt2)
  else
    count_mem pt1 pts + (pt1 == pt2).
Proof.
rewrite /insert_factor.
case: ifP => _; rewrite eq_sym.
- exact: count_mem_rem.
- exact: addnC.
Qed.

(* [count_cancel] without list-atomicity: for a single *atomic* [pt] the count
   formula holds on any wf list.  (In the [pt = pt'] recursion [pt'] is atomic
   because it equals [pt]; products in the tail never interfere.) *)
Lemma count_cancel pt pts :
  wf_term pt -> ~~ is_mul pt -> all wf_term pts ->
  count_mem pt (cancel_invs pts) = count_mem pt pts - count_mem (inv_aux pt) pts.
Proof.
elim: pts => //= [pt' pts' IH] in pt * => wfpt Nmpt /andP [wfpt' wfpts'].
rewrite count_insert_factor eq_sym.
case: (pt =P pt') => [<-{pt' wfpt'} | /eqP/negbTE neq].
- rewrite eqxx (negbTE (inv_aux_Nid pt)) [in RHS]eq_sym (negbTE (inv_aux_Nid pt)).
  case: ifP => /count_memPn /eqP;
    rewrite !IH ?wf_inv_aux ?is_mul_inv_aux // inv_auxK //.
  + by rewrite -ltnNge => /[dup] /eqP -> /ltnW /eqP ->.
  + rewrite addnC. exact: addnBA.
- rewrite [pt' == pt]eq_sym neq add0n addn0.
  case: ifP => [_ | /count_memPn /eqP wt0]; rewrite -inv_aux_eq_op // eq_sym.
  + by rewrite IH // subBnAC.
  + move: wt0. case: (pt =P inv_aux pt') => [<- | _ _]; rewrite IH //.
    by rewrite -subBnAC => /eqP ->.
Qed.

(* Forward direction only — the [perm_eq -> forall pt] converse is unused and
   would need [count_cancel] on arbitrary (possibly product) [pt], which no longer
   holds now that [wf_inv_aux] requires atomicity. *)
Lemma count_perm_cancel pts1 pts2 :
  all wf_term pts1 -> all (fun t => ~~ is_mul t) pts1 ->
  all wf_term pts2 -> all (fun t => ~~ is_mul t) pts2 ->
  (forall pt, wf_term pt -> ~~ is_mul pt ->
         count_mem pt pts1 - count_mem (inv_aux pt) pts1 =
         count_mem pt pts2 - count_mem (inv_aux pt) pts2) ->
  perm_eq (cancel_invs pts1) (cancel_invs pts2).
Proof.
move => wfs1 Nms1 wfs2 Nms2 wt_eq. rewrite /perm_eq.
apply /allP => /= pt; rewrite mem_cat => /orP [] /mem_cancel_invs h.
- have wfpt := allP wfs1 _ h; have Nmpt := allP Nms1 _ h.
  by rewrite !count_cancel // wt_eq.
- have wfpt := allP wfs2 _ h; have Nmpt := allP Nms2 _ h.
  by rewrite !count_cancel // wt_eq.
Qed.

(* A product [pt] passes through [cancel_invs] untouched: its factor-level
   inverse [inv_aux pt = PTInv pt] is ill-formed (a [PTInv] of a product), so it
   is absent from any wf list and [pt] never cancels. *)
Lemma count_cancel_mul pt pts :
  is_mul pt -> all wf_term pts ->
  count_mem pt (cancel_invs pts) = count_mem pt pts.
Proof.
move=> Mpt; elim: pts => //= [pt' pts' IH] /andP [wfpt' wfpts'].
rewrite count_insert_factor IH //.
have Ne : (pt == inv_aux pt') = false.
  by apply/negbTE/eqP => e; move: Mpt; rewrite e (negbTE (is_mul_inv_aux wfpt')).
case: ifP => [Hin | _]; last by rewrite [pt' == pt]eq_sym addnC.
rewrite Ne subn0.
suff -> : (pt' == pt) = false by [].
apply/negbTE/eqP => e; move: Hin; rewrite e => Hin.
move: (allP (wf_cancel_invs wfpts') _ Hin) Mpt.
by case: (pt) => //=.
Qed.

Lemma perm_cancel_invs pts1 pts2 :
  all wf_term pts1 -> perm_eq pts1 pts2 ->
  perm_eq (cancel_invs pts1) (cancel_invs pts2).
Proof.
move=> wf1 peq.
have wf2 : all wf_term pts2 by rewrite -(perm_all _ peq).
rewrite /perm_eq; apply/allP => /= pt; rewrite mem_cat => /orP[] /mem_cancel_invs h.
- have wfpt := allP wf1 _ h; apply/eqP.
  have [Mpt|Nmpt] := boolP (is_mul pt).
  + by rewrite !count_cancel_mul // (permP peq).
  + by rewrite !count_cancel // !(permP peq).
- have wfpt := allP wf2 _ h; apply/eqP.
  have [Mpt|Nmpt] := boolP (is_mul pt).
  + by rewrite !count_cancel_mul // (permP peq).
  + by rewrite !count_cancel // !(permP peq).
Qed.

Lemma inv_invN pt : ~~ is_inv pt -> inv_aux pt = PTInv pt.
Proof. by case: pt => - []. Qed.

Lemma base_exp b e : wf_term b -> base (exp b e) = base b.
Proof. by move => wf; rewrite /exp; case: ifP => _ //; rewrite base_idem. Qed.

Lemma exps_expN pt : ~~ is_exp pt -> exps pt = [::].
Proof. by move => ?; rewrite /exps expo_expN. Qed.

Lemma exps_base pt : wf_term pt -> exps (base pt) = [::].
Proof. by move => wf; rewrite exps_expN // base_Nexp. Qed.

Lemma base_expoK pt : is_exp pt -> PTExp (base pt) (expo pt) = pt.
Proof. by case: pt => [o|o t|[||] t1 t2|ts]. Qed.

(* [inv_aux] (the factor-level inverse) is inverted back by the real [inv]. *)
Lemma inv_inv_aux pt : wf_term pt -> inv (inv_aux pt) = pt.
Proof.
move=> wf; have Nm := is_mul_inv_aux wf.
rewrite (_ : inv (inv_aux pt) = inv_aux (inv_aux pt));
  last by rewrite /inv; case: (inv_aux pt) Nm.
exact: inv_auxK.
Qed.

(* Being canceled under the real [inv] implies being canceled under [inv_aux]:
   an [inv_aux]-pair always induces an [inv]-pair (the [O1Inv] wrapper is not a
   product, so its real inverse is the unwrapped element). *)
Lemma invs_canceled_inv_aux pts :
  all wf_term pts -> invs_canceled pts -> all (fun pt => inv_aux pt \notin pts) pts.
Proof.
move=> /allP wfs /allP canc; apply/allP => pt pt_pts; apply/negP => inv_aux_in.
by move: (canc _ inv_aux_in); rewrite (inv_inv_aux (wfs _ pt_pts)) pt_pts.
Qed.

(* On atomic lists [inv = inv_aux], so [invs_canceled] reduces to the naive form. *)
Lemma invs_canceled_atomic pts :
  all (fun pt => ~~ is_mul pt) pts ->
  invs_canceled pts = all (fun pt => inv_aux pt \notin pts) pts.
Proof.
move=> /allP atom; rewrite /invs_canceled; apply: eq_in_all => pt pt_pts.
have Nm := atom _ pt_pts; clear pt_pts.
by move: Nm; rewrite /inv; case: pt.
Qed.

Lemma invs_canceled_sort pts : invs_canceled (sort <=%O pts) = invs_canceled pts.
Proof. rewrite /invs_canceled all_sort. apply eq_all => ?. by rewrite mem_sort. Qed.

(* [cancel_invs]/[insert_factor] produce lists with no [inv_aux]-pair (the underlying
   cancellation algorithm operates on [inv_aux]). *)
Lemma insert_factor_no_pair pt pts :
  wf_term pt -> all wf_term pts ->
  all (fun q => inv_aux q \notin pts) pts ->
  all (fun q => inv_aux q \notin insert_factor pt pts) (insert_factor pt pts).
Proof.
move => ? /allP /= wfs /allP /= canceled.
apply /allP. rewrite /insert_factor /= => pt'.
case: ifP => [_| /negP ?].
- move => /mem_rem /canceled. apply: contra. exact: mem_rem.
- rewrite !inE negb_or => /orP [/eqP -> | in_pts].
  + rewrite inv_aux_Nid. exact /negP.
  + apply /andP; split; last exact: canceled.
    have ? := wfs _ in_pts.
    apply /eqP => /eqP. rewrite inv_aux_eq_op // => /eqP eq.
    by rewrite eq in in_pts.
Qed.

Lemma cancel_invs_no_pair pts :
  all wf_term pts ->
  all (fun q => inv_aux q \notin cancel_invs pts) (cancel_invs pts).
Proof.
elim: pts => // [?? IH] /andP [??].
apply insert_factor_no_pair => //.
  exact: wf_cancel_invs.
  exact: IH.
Qed.

(* On atomic input [cancel_invs] output is real-[inv]-canceled too. *)
Lemma invs_canceled_cancel_invs pts :
  all (fun pt => ~~ is_mul pt) pts -> all wf_term pts ->
  invs_canceled (cancel_invs pts).
Proof.
move=> atom wf.
by rewrite (invs_canceled_atomic (Nmul_cancel_invs atom)); exact: cancel_invs_no_pair.
Qed.

Lemma invs_canceled_cons pt pts : invs_canceled (pt :: pts) -> invs_canceled pts.
Proof.
rewrite /invs_canceled => /andP [_ /allP canceled].
apply /allP => ? /canceled.
by rewrite inE negb_or => /andP [].
Qed.

(* No [inv_aux]-pair in the input ⇒ [cancel_invs] is the identity. *)
Lemma no_pair_cons pt pts :
  all (fun q => inv_aux q \notin (pt :: pts)) (pt :: pts) ->
  all (fun q => inv_aux q \notin pts) pts.
Proof.
move=> /andP [_ /allP canceled]; apply/allP => ? /canceled.
by rewrite inE negb_or => /andP [].
Qed.

Lemma insert_factor_id pt pts :
  all (fun q => inv_aux q \notin (pt :: pts)) (pt :: pts) ->
  insert_factor pt pts = pt :: pts.
Proof.
move=> /allP canceled; rewrite /insert_factor.
have := canceled _ (mem_head _ _).
by rewrite inE negb_or => /andP [_ /negbTE ->].
Qed.

Lemma cancel_invs_id pts :
  all (fun q => inv_aux q \notin pts) pts -> cancel_invs pts = pts.
Proof.
elim: pts => // [pt pts IH] canceled /=.
rewrite (IH (no_pair_cons canceled)).
exact: (insert_factor_id canceled).
Qed.

Lemma cancel_invs_canceled pts :
  all (fun pt => ~~ is_mul pt) pts -> invs_canceled pts -> cancel_invs pts = pts.
Proof. by move=> atom; rewrite (invs_canceled_atomic atom); exact: cancel_invs_id. Qed.

Lemma invs_canceled1 t : ~~ is_mul t -> invs_canceled [:: t].
Proof.
move=> Nm; rewrite invs_canceled_atomic; last by rewrite /= Nm.
by rewrite /= andbT !inE inv_aux_Nid.
Qed.

Lemma invs_canceled_factors pt : wf_term pt -> invs_canceled (factors pt).
Proof.
case: pt => [o|o t|o t1 t2|ts] wf; rewrite /factors;
  try by apply: invs_canceled1.
by case/and5P: wf.
Qed.

Lemma sorted_factors pt : wf_term pt -> sorted <=%O (factors pt).
Proof.
case: pt => [o|o t|o t1 t2|ts] wf; rewrite /factors; try by [].
by case/and5P: wf.
Qed.

Lemma invs_canceled_exps pt : wf_term pt -> invs_canceled (exps pt).
Proof. by move => wf; rewrite /exps; apply/invs_canceled_factors/wf_expo. Qed.

Lemma exps_sorted pt : wf_term pt -> sorted <=%O (exps pt).
Proof. by move => wf; rewrite /exps; apply/sorted_factors/wf_expo. Qed.

Lemma cancel_invs_exps pt :
  wf_term pt -> cancel_invs (exps pt) = exps pt.
Proof.
move => wf. apply: cancel_invs_canceled; last exact: invs_canceled_exps.
by rewrite /exps; apply/Nmul_factors/wf_expo.
Qed.

(* Multiplication *)

Lemma flatten_factors_wf ts :
  all wf_term ts -> all wf_term (flatten [seq factors t | t <- ts]).
Proof.
elim: ts => //= t ts IH /andP [wf_t /IH ?].
by rewrite all_cat wf_factors.
Qed.

Lemma flatten_factors_Nmul ts :
  all wf_term ts -> all (fun t => ~~ is_mul t) (flatten [seq factors t | t <- ts]).
Proof.
elim: ts => //= t ts IH /andP [wf_t /IH ?].
by rewrite all_cat Nmul_factors.
Qed.

Lemma factors_mul ts :
  all wf_term ts ->
  factors (mul ts) = sort <=%O (cancel_invs (flatten [seq factors t | t <- ts])).
Proof.
move => wf; rewrite /mul.
set c := cancel_invs _.
have Nmul_c : all (fun t => ~~ is_mul t) c.
  apply/allP => x /mem_cancel_invs xin.
  by move/allP: (flatten_factors_Nmul wf) => /(_ x xin).
case E: (sort <=%O c) => [|t [|t' c']] //=.
have : t \in sort <=%O c by rewrite E mem_head.
by rewrite mem_sort => /(allP Nmul_c) /factorsN ->.
Qed.

Lemma wf_mul ts : all wf_term ts -> wf_term (mul ts).
Proof.
move => wf; rewrite /mul.
set c := cancel_invs _.
have wf_c : all wf_term c by apply: wf_cancel_invs; exact: flatten_factors_wf.
have wf_sc : all wf_term (sort <=%O c) by rewrite all_sort.
have Nmul_sc : all (fun t => ~~ is_mul t) (sort <=%O c).
  rewrite all_sort; apply/allP => x /mem_cancel_invs xin.
  by move/allP: (flatten_factors_Nmul wf) => /(_ x xin).
have sorted_sc : sorted <=%O (sort <=%O c) by exact: sort_le_sorted.
have inv_sc : invs_canceled (sort <=%O c).
  rewrite invs_canceled_sort; apply: invs_canceled_cancel_invs.
  - exact: flatten_factors_Nmul wf.
  - exact: flatten_factors_wf.
case E: (sort <=%O c) => [|t [|t' c']] //=.
  have : t \in sort <=%O c by rewrite E mem_head.
  by rewrite mem_sort => /(allP wf_c).
move: wf_sc Nmul_sc sorted_sc inv_sc; rewrite E => wf' Nmul' sorted' inv_aux'.
by apply/and5P; split.
Qed.

Lemma perm_mul ts1 ts2 :
  all wf_term ts1 -> perm_eq ts1 ts2 -> mul ts1 = mul ts2.
Proof.
move => wf1 peq.
have wf2 : all wf_term ts2 by rewrite -(perm_all _ peq).
rewrite /mul.
have -> : sort <=%O (cancel_invs (flatten [seq factors t | t <- ts1])) =
          sort <=%O (cancel_invs (flatten [seq factors t | t <- ts2])).
  apply/perm_sort_leP/perm_cancel_invs;
    [exact: flatten_factors_wf | by rewrite perm_flatten // perm_map].
by [].
Qed.

Lemma mul_wf1 t : wf_term t -> mul [:: t] = t.
Proof.
move => wf; rewrite /mul /= cats0.
rewrite (cancel_invs_canceled (Nmul_factors wf) (invs_canceled_factors wf)).
rewrite sort_le_id ?sorted_factors //.
case: t wf => [o|o t|o t1 t2|ts] //= wf.
by case/and5P: wf => _ _ _ _; case: ts => [|t [|t' c']].
Qed.

Lemma expo_exp b : expo b != PTMul [::] -> is_exp b.
Proof. by case: b => [o|o t|[||] t1 t2|ts] //=; rewrite eqxx. Qed.

Lemma expo_unit_Nexp b : wf_term b -> expo b = PTMul [::] -> ~~ is_exp b.
Proof.
case: b => [o|o t|[||] t1 t2|ts] //= /and4P [_ _ _ eN0] e0.
by move: eN0; rewrite e0 eqxx.
Qed.

Lemma exps_exp b e :
  wf_term b -> wf_term e ->
  exps (exp b e) = sort <=%O (cancel_invs (exps b ++ factors e)).
Proof.
move => wfb wfe.
have wf' : all wf_term [:: expo b; e] by rewrite /= (wf_expo wfb) wfe.
have key : exps (exp b e) = factors (mul [:: expo b; e]).
  rewrite /exp; case: (eqVneq (mul [:: expo b; e]) (PTMul [::])) => [heq|hne].
  - by rewrite heq /= (exps_expN (base_Nexp wfb)).
  - by rewrite /exps /expo.
by rewrite key factors_mul //= cats0 /exps.
Qed.

Lemma wf_exp b e : wf_term b -> wf_term e -> wf_term (exp b e).
Proof.
move => wfb wfe; rewrite /exp; case: ifP => [_|Hf].
  exact: wf_base.
have wf' : all wf_term [:: expo b; e] by rewrite /= (wf_expo wfb) wfe.
by rewrite /= wf_base //= base_Nexp //= wf_mul //= Hf.
Qed.

Lemma is_exp_exp b e :
  wf_term b -> is_exp (exp b e) = (mul [:: expo b; e] != PTMul [::]).
Proof.
move => wfb; rewrite /exp; case: eqP => [_ | ne] /=.
- by rewrite (negbTE (base_Nexp wfb)).
- by [].
Qed.

Lemma exp_unit b : wf_term b -> exp b (PTMul [::]) = b.
Proof.
move => wf; rewrite /exp.
have -> : mul [:: expo b; PTMul [::]] = expo b.
  have -> : mul [:: expo b; PTMul [::]] = mul [:: expo b] by rewrite /mul /= !cats0.
  exact: mul_wf1 (wf_expo wf).
have [e0|eN0] := eqVneq (expo b) (PTMul [::]).
  by rewrite (base_expN (expo_unit_Nexp wf e0)).
by rewrite (base_expoK (expo_exp eN0)).
Qed.

Lemma flatten_factors_Nmul_id us :
  all (fun t => ~~ is_mul t) us -> flatten [seq factors t | t <- us] = us.
Proof.
elim: us => //= u us' IH /andP [Nu Nus'].
by rewrite (factorsN Nu) /= IH.
Qed.

Lemma mul_factors pt : wf_term pt -> mul (factors pt) = pt.
Proof.
case: pt => [o|o t|o t1 t2|ts] wf; rewrite /factors; try exact: (mul_wf1 wf).
move: wf => /and5P [_ Nmul sorted_ts inv_ts sizeN1]; rewrite /mul.
rewrite (flatten_factors_Nmul_id Nmul) (cancel_invs_canceled Nmul inv_ts) sort_le_id //.
by case: ts sizeN1 {Nmul sorted_ts inv_ts} => [|? [|? ?]].
Qed.

Lemma exp_base_expo pt : wf_term pt -> exp (base pt) (expo pt) = pt.
Proof.
case: pt => [o|o t|[||] t1 t2|ts] wf //=; rewrite ?(exp_unit wf) //.
case/and4P: wf => wfb Nxb wfe eN0.
rewrite /exp (expo_expN Nxb).
have -> : mul [:: PTMul [::]; t2] = t2.
  have -> : mul [:: PTMul [::]; t2] = mul [:: t2] by rewrite /mul /= !cats0.
  exact: mul_wf1.
by rewrite (negbTE eN0) (base_expN Nxb).
Qed.

Lemma tsize_exp_Nexp b e :
  ~~ is_exp b -> wf_term e -> e != PTMul [::] ->
  tsize (exp b e) = S (tsize b + tsize e).
Proof.
move => Nxb wfe eN0; rewrite /exp.
have -> : mul [:: expo b; e] = e.
  rewrite expo_expN //.
  have -> : mul [:: PTMul [::]; e] = mul [:: e] by rewrite /mul /= !cats0.
  exact: mul_wf1.
by rewrite (negbTE eN0) base_expN.
Qed.

Lemma inv_Nmul pt : ~~ is_mul pt -> inv pt = inv_aux pt.
Proof. by case: pt. Qed.

Lemma wf_inv pt : wf_term pt -> wf_term (inv pt).
Proof.
case: pt => [o|[k| |] t|o t1 t2|ts] wf; rewrite /inv /=.
- exact: (wf_inv_aux wf isT).
- exact: (wf_inv_aux wf isT).
- exact: (wf_inv_aux wf isT).
- by case/and3P: wf.
- exact: (wf_inv_aux wf isT).
- apply: wf_mul; rewrite all_map; case/and5P: wf => wf_ts Nm_ts _ _ _.
  apply/allP => t t_ts; apply: wf_inv_aux;
  [exact: (allP wf_ts) | exact: (allP Nm_ts)].
Qed.

(* Uniform view of [inv]: distribute [inv_aux] over the factors and re-fold.  Holds
   for products (by definition) and non-products (where [factors pt = [:: pt]] and
   [mul [:: inv_aux pt] = inv_aux pt]). *)
Lemma inv_factors pt : wf_term pt -> inv pt = mul (map inv_aux (factors pt)).
Proof.
case: pt => [o|o t|o t1 t2|ts] wf; rewrite /inv /factors //=;
  by rewrite (mul_wf1 (wf_inv_aux wf isT)).
Qed.

Lemma wf_normalize pt : wf_term (normalize pt).
Proof.
elim: pt => //=.
- by case=> [k|| ] t IH /=; [exact: IH|exact: IH|exact: wf_inv].
- move => o t1 IH1 t2 IH2; case: o => /=; try by rewrite IH1 IH2.
  by apply: wf_exp.
- move => ts IHts; apply: wf_mul.
  by elim: ts IHts => //= t ts' IH [wt wts]; rewrite wt; exact: IH wts.
Qed.

Lemma normalize_wf pt : wf_term pt -> normalize pt = pt.
Proof.
elim: pt => //=.
- case=> [k|| ] t IH /=.
  + by move => wf; rewrite (IH wf).
  + by move => wf; rewrite (IH wf).
  + by move => /and3P [ni nm wf]; rewrite (IH wf) (inv_Nmul nm) (inv_invN ni).
- move => o t1 IH1 t2 IH2; case: o => /=.
  + by move => /andP [/IH1 -> /IH2 ->].
  + by move => /andP [/IH1 -> /IH2 ->].
  + move => /and4P [wfb Nxb wfe eN0].
    rewrite IH1 // IH2 // /exp expo_expN // base_expN //.
    have -> : mul [:: PTMul [::]; t2] = t2.
      have -> : mul [:: PTMul [::]; t2] = mul [:: t2] by rewrite /mul /= !cats0.
      exact: mul_wf1.
    by rewrite (negbTE eN0).
- move => ts IHts /and5P [wf_ts Nmul_ts sorted_ts inv_ts sizeN1].
  have Nts : map normalize ts = ts.
    elim: ts IHts wf_ts {Nmul_ts sorted_ts inv_ts sizeN1}
      => //= t ts' IH [IHt IHts'] /andP [wt wts].
    by rewrite IHt // IH.
  rewrite Nts /mul.
  have ff : flatten [seq factors t | t <- ts] = ts.
    elim: ts Nmul_ts {IHts wf_ts sorted_ts inv_ts sizeN1 Nts}
      => //= t ts' IH /andP [Nt Nts'].
    by rewrite (factorsN Nt) /= IH.
  rewrite ff cancel_invs_canceled // sort_le_id //.
  by case: ts sizeN1 {IHts wf_ts Nmul_ts sorted_ts inv_ts Nts ff} => // t [|??].
Qed.

Lemma normalize_idem : idempotent_fun normalize.
Proof. move => ?. apply: normalize_wf; exact: wf_normalize. Qed.

Lemma tsize_inv pt : ~~ is_inv pt -> tsize (inv_aux pt) = S (tsize pt).
Proof. move => ?. by rewrite inv_invN. Qed.

Lemma mulP ts1 ts2 :
  perm_eq (cancel_invs (flatten [seq factors t | t <- ts1]))
          (cancel_invs (flatten [seq factors t | t <- ts2])) ->
  mul ts1 = mul ts2.
Proof. by rewrite /mul => /perm_sort_leP ->. Qed.

Lemma cancel_invs_cat pts1 pts2 :
  all wf_term pts1 -> all (fun t => ~~ is_mul t) pts1 ->
  all wf_term pts2 -> all (fun t => ~~ is_mul t) pts2 ->
  perm_eq (cancel_invs (cancel_invs pts1 ++ pts2)) (cancel_invs (pts1 ++ pts2)).
Proof.
move => wf1 Nm1 wf2 Nm2; apply count_perm_cancel.
- by rewrite all_cat (wf_cancel_invs wf1) wf2.
- by rewrite all_cat (Nmul_cancel_invs Nm1) Nm2.
- by rewrite all_cat wf1 wf2.
- by rewrite all_cat Nm1 Nm2.
move => pt wfpt Nmpt; rewrite !count_cat count_cancel //.
rewrite count_cancel // ?is_mul_inv_aux // ?wf_inv_aux // ?inv_auxK //.
by rewrite !addnE !subnE; lia.
Qed.

Lemma mul_cat ts1 ts2 :
  all wf_term ts1 -> all wf_term ts2 ->
  mul (mul ts1 :: ts2) = mul (ts1 ++ ts2).
Proof.
move => wf1 wf2; apply: mulP.
rewrite map_cons /= (factors_mul wf1) map_cat flatten_cat.
apply: perm_trans;
  last exact: (cancel_invs_cat (flatten_factors_wf wf1) (flatten_factors_Nmul wf1)
                               (flatten_factors_wf wf2) (flatten_factors_Nmul wf2)).
apply: perm_cancel_invs.
- by rewrite all_cat all_sort (wf_cancel_invs (flatten_factors_wf wf1))
             (flatten_factors_wf wf2).
- by rewrite perm_cat2r perm_sort.
Qed.

Lemma sortcancel_catr A B :
  all wf_term A -> all (fun t => ~~ is_mul t) A ->
  all wf_term B -> all (fun t => ~~ is_mul t) B ->
  sort <=%O (cancel_invs (A ++ sort <=%O (cancel_invs B))) =
  sort <=%O (cancel_invs (A ++ B)).
Proof.
move => wfA NmA wfB NmB; apply/perm_sort_leP.
have wfcB := wf_cancel_invs wfB.
have NmcB := Nmul_cancel_invs NmB.
apply: (perm_trans (y := cancel_invs (A ++ cancel_invs B))).
  apply: perm_cancel_invs.
  - by rewrite all_cat wfA all_sort wfcB.
  - by rewrite perm_cat2l perm_sort.
apply: (perm_trans (y := cancel_invs (cancel_invs B ++ A))).
  apply: perm_cancel_invs.
  - by rewrite all_cat wfA wfcB.
  - by rewrite perm_catC.
apply: (perm_trans (y := cancel_invs (B ++ A))).
  exact: (cancel_invs_cat wfB NmB wfA NmA).
apply: perm_cancel_invs.
- by rewrite all_cat wfB wfA.
- by rewrite perm_catC.
Qed.

Lemma expo_exp_eq b e : wf_term b -> expo (exp b e) = mul [:: expo b; e].
Proof.
move => wfb; rewrite /exp.
case: (eqVneq (mul [:: expo b; e]) (PTMul [::])) => [heq|hne].
- by rewrite heq (expo_expN (base_Nexp wfb)).
- by rewrite /expo.
Qed.

Lemma expA b e1 e2 :
  wf_term b -> wf_term e1 -> wf_term e2 ->
  exp (exp b e1) e2 = exp b (mul [:: e1; e2]).
Proof.
move => wfb wfe1 wfe2.
have wfeb := wf_expo wfb.
have wfm : wf_term (mul [:: e1; e2]) by apply: wf_mul; rewrite /= wfe1 wfe2.
have key : mul [:: mul [:: expo b; e1]; e2] = mul [:: expo b; mul [:: e1; e2]].
  rewrite (mul_cat (ts1 := [:: expo b; e1]) (ts2 := [:: e2]));
    [| by rewrite /= wfeb wfe1 | by rewrite /= wfe2].
  rewrite (perm_mul (ts1 := [:: expo b; mul [:: e1; e2]])
                    (ts2 := [:: mul [:: e1; e2]; expo b]));
    [| by rewrite /= wfeb wfm | by apply/permP => x /=; rewrite !addnE; lia].
  rewrite (mul_cat (ts1 := [:: e1; e2]) (ts2 := [:: expo b]));
    [| by rewrite /= wfe1 wfe2 | by rewrite /= wfeb].
  apply: perm_mul; first by rewrite /= wfe1 wfe2 wfeb.
  by apply/permP => x /=; rewrite !addnE; lia.
by rewrite {1}/exp base_exp // (expo_exp_eq _ wfb) key.
Qed.

Lemma mul_mul2 ts1 ts2 :
  all wf_term ts1 -> all wf_term ts2 ->
  mul [:: mul ts1; mul ts2] = mul (ts1 ++ ts2).
Proof.
move => wf1 wf2.
have wfm2 : wf_term (mul ts2) := wf_mul wf2.
rewrite (mul_cat (ts1 := ts1) (ts2 := [:: mul ts2])); [| exact: wf1 | by rewrite /= wfm2].
rewrite (perm_mul (ts1 := ts1 ++ [:: mul ts2]) (ts2 := mul ts2 :: ts1));
  [| by rewrite all_cat wf1 /= wfm2 | by rewrite -cat1s perm_catC].
rewrite (mul_cat (ts1 := ts2) (ts2 := ts1)); [| exact: wf2 | exact: wf1].
apply: perm_mul; first by rewrite all_cat wf2 wf1.
by rewrite perm_catC.
Qed.

Lemma count_map_inv pt ts :
  wf_term pt -> all wf_term ts ->
  count_mem pt (map inv_aux ts) = count_mem (inv_aux pt) ts.
Proof.
move => wfpt wf; rewrite count_map; apply: eq_in_count => t /(allP wf) wft.
by rewrite /= (inv_aux_eq_op wft wfpt).
Qed.

Lemma cancel_invs_invs ts :
  all wf_term ts -> all (fun t => ~~ is_mul t) ts ->
  cancel_invs (ts ++ map inv_aux ts) = [::].
Proof.
move => wf Nm.
have wfinv : all wf_term (map inv_aux ts).
  rewrite all_map; apply/allP => t t_ts.
  by apply: wf_inv_aux; [exact: (allP wf) | exact: (allP Nm)].
have Nminv : all (fun t => ~~ is_mul t) (map inv_aux ts).
  by rewrite all_map; apply/allP => t t_ts; apply: is_mul_inv_aux; exact: (allP wf).
suff : perm_eq (cancel_invs (ts ++ map inv_aux ts)) (cancel_invs [::]).
  by move/perm_nilP.
apply count_perm_cancel; rewrite ?all_cat ?wf ?Nm ?wfinv ?Nminv //.
move => pt wfpt Nmpt.
have e : count_mem pt (ts ++ map inv_aux ts)
         = count_mem (inv_aux pt) (ts ++ map inv_aux ts).
  rewrite !count_cat (count_map_inv wfpt wf)
          (count_map_inv (wf_inv_aux wfpt Nmpt) wf) (inv_auxK wfpt).
  exact: addnC.
by rewrite e /= subnn.
Qed.

Lemma mul_invs ts :
  all wf_term ts -> all (fun t => ~~ is_mul t) (ts ++ map inv_aux ts) ->
  mul (ts ++ map inv_aux ts) = PTMul [::].
Proof.
move => wf atom.
have Nm : all (fun t => ~~ is_mul t) ts by move: atom; rewrite all_cat => /andP [].
by rewrite /mul (flatten_factors_Nmul_id atom) (cancel_invs_invs wf Nm).
Qed.

Lemma mul_eq_unit ts :
  all (fun t => ~~ is_mul t) ts -> invs_canceled ts ->
  (mul ts == PTMul [::]) = (ts == [::]).
Proof.
move => atom canc.
rewrite -size_eq0 -(size_sort <=%O ts) size_eq0.
rewrite /mul (flatten_factors_Nmul_id atom) (cancel_invs_canceled atom canc).
case E: (sort <=%O ts) => [|a [|b l]] //=.
have : a \in ts by rewrite -(mem_sort <=%O ts) E mem_head.
by move/(allP atom); case: (a) => // - [].
Qed.

Lemma tsize_mul ts :
  all (fun t => ~~ is_mul t) ts -> invs_canceled ts -> ts != [::] ->
  tsize (mul ts) = (1 < size ts) + sumn [seq tsize t | t <- ts].
Proof.
move => atom canc tsN0.
rewrite /mul (flatten_factors_Nmul_id atom) (cancel_invs_canceled atom canc).
have <- : size (sort <=%O ts) = size ts by rewrite size_sort.
have <- : sumn [seq tsize t | t <- sort <=%O ts] = sumn [seq tsize t | t <- ts].
  rewrite !sumnE !big_map; apply: perm_big; by rewrite perm_sort.
have : sort <=%O ts != [::] by rewrite -size_eq0 size_sort size_eq0.
case: (sort <=%O ts) => [|a [|b l]] // _.
- by rewrite /= add0n addn0.
- by rewrite sumnE.
Qed.

Lemma invs_canceled_map_inv ts :
  all wf_term ts -> invs_canceled ts -> invs_canceled (map inv_aux ts).
Proof.
move => wf canc; apply/allP => x /mapP [t t_ts ->].
have wft := allP wf _ t_ts.
rewrite (inv_inv_aux wft); apply/negP => /mapP [s s_ts e].
have ws := allP wf _ s_ts.
by move: (allP canc _ t_ts); rewrite e (inv_inv_aux ws) s_ts.
Qed.

Lemma invK pt : wf_term pt -> inv (inv pt) = pt.
Proof.
move => wf.
have fs_wf := wf_factors wf.
have fs_Nm := Nmul_factors wf.
have fs_canc := invs_canceled_factors wf.
have wfinv : all wf_term (map inv_aux (factors pt)).
  rewrite all_map; apply/allP => t t_fs.
  by apply: wf_inv_aux; [exact: (allP fs_wf) | exact: (allP fs_Nm)].
have Nminv : all (fun t => ~~ is_mul t) (map inv_aux (factors pt)).
  by rewrite all_map; apply/allP => t t_fs; apply: is_mul_inv_aux; exact: (allP fs_wf).
have canc_inv := invs_canceled_map_inv fs_wf fs_canc.
have mapK : map inv_aux (map inv_aux (factors pt)) = factors pt.
  rewrite -map_comp -[RHS]map_id; apply/eq_in_map => t t_fs.
  exact: (inv_auxK (allP fs_wf _ t_fs)).
rewrite (inv_factors wf) (inv_factors (wf_mul wfinv)).
rewrite (factors_mul wfinv) (flatten_factors_Nmul_id Nminv)
        (cancel_invs_canceled Nminv canc_inv).
rewrite -{2}(mul_factors wf).
apply: perm_mul.
- rewrite all_map; apply/allP => t; rewrite mem_sort => t_in.
  apply: wf_inv_aux; [exact: (allP wfinv) | exact: (allP Nminv)].
- apply: (perm_trans (y := map inv_aux (map inv_aux (factors pt)))).
  + by rewrite perm_map // perm_sort.
  + by rewrite mapK.
Qed.

(* The inverse of a non-empty canonical product is a *different* product: a
   canonical factor list has no [inv_aux]-pairs, so inverting every factor
   cannot reproduce the same list.  Hence the identity [PTMul []] is the unique
   self-inverse well-formed pre-term (see [inv_fixed]). *)
Lemma mul_map_inv_aux_neq us :
  all wf_term us -> all (fun t => ~~ is_mul t) us ->
  invs_canceled us -> us != [::] -> mul (map inv_aux us) != PTMul us.
Proof.
move=> wfs atoms canc usN0.
have wfI : all wf_term (map inv_aux us).
  apply/allP => x /mapP [t t_in ->]; apply: wf_inv_aux;
  [exact: (allP wfs) | exact: (allP atoms)].
have atomI : all (fun t => ~~ is_mul t) (map inv_aux us).
  by apply/allP => x /mapP [t t_in ->]; exact: is_mul_inv_aux (allP wfs _ t_in).
have cancI : invs_canceled (map inv_aux us) := invs_canceled_map_inv wfs canc.
apply/negP => /eqP E.
have factE : factors (mul (map inv_aux us)) = sort <=%O (map inv_aux us).
  rewrite (factors_mul wfI) (flatten_factors_Nmul_id atomI).
  by rewrite (cancel_invs_canceled atomI cancI).
move: factE; rewrite E /= => sortE.
have perm_us : perm_eq us (map inv_aux us) by rewrite {1}sortE perm_sort.
have [u u_us] : exists u, u \in us by case: (us) usN0 => [|x ?] // _; exists x; rewrite mem_head.
have inus : inv_aux u \in us by rewrite (perm_mem perm_us); apply/mapP; exists u.
by move: (allP canc _ u_us); rewrite (inv_Nmul (allP atoms _ u_us)) inus.
Qed.

(* [PTMul []] is the unique fixed point of the (distributing) inverse. *)
Lemma inv_fixed pt : wf_term pt -> (inv pt == pt) = (pt == PTMul [::]).
Proof.
move=> wf; case: (boolP (is_mul pt)) => [mul_pt|Nm]; last first.
  rewrite (inv_Nmul Nm) (negbTE (inv_aux_Nid _)).
  by case: pt Nm {wf} => //= ts; case: ts.
case: pt mul_pt wf => // us _ wf.
have -> : inv (PTMul us) = mul (map inv_aux us) by [].
move: wf => /and5P [wfs atoms _ canc _].
case: (altP (us =P [::])) => [->|usN0]; first by rewrite /mul /= !eqxx.
rewrite (negbTE (mul_map_inv_aux_neq wfs atoms canc usN0)).
by apply/esym; apply/eqP => - [] /eqP; rewrite (negbTE usN0).
Qed.

Module Exports.
HB.reexport.
End Exports.

End PreTerm.

Export PreTerm.Exports.
