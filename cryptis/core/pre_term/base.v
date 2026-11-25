From cryptis Require Export mathcomp_compat.
From HB Require Import structures.
From mathcomp Require Import order boot.
From deriving Require Import deriving.
From Stdlib Require Import ZArith.ZArith Lia.
From iris.heap_lang Require locations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.POrderTheory Order.TotalTheory.

(* A nonce is a nominal wrapper around a heap location. *)
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

Abbreviation TInt_tag := 0%Z.
Abbreviation TNonce_tag := 1%Z.

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
| O1Hash.

Abbreviation TKey_tag := 0%Z.
Abbreviation THash_tag := 1%Z.

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

Abbreviation TPair_tag := 0%Z.
Abbreviation TSeal_tag := 1%Z.

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

Abbreviation TOp0_tag := 0%Z.
Abbreviation TOp1_tag := 1%Z.
Abbreviation TOp2_tag := 2%Z.
Abbreviation TMul_tag := 3%Z.
Abbreviation TDH_tag := 4%Z.

Module PreTerm.

(** [PTMul ps ns] is a product in the group of exponents.  [PTDH l] is a
    Diffie-Hellman term: [l] maps each base to its logarithm, a formal sum of
    exponents given by its positive and its negative exponents. *)
Unset Elimination Schemes.
Inductive pre_term :=
| PT0 of term_op0
| PT1 of term_op1 & pre_term
| PT2 of term_op2 & pre_term & pre_term
| PTMul of list pre_term & list pre_term
| PTDH of list (pre_term * (list pre_term * list pre_term)).
Set Elimination Schemes.

(* [deriving] treats the nested types as further sorts of a mutual family: the
   lists of pre-terms, the logarithms, the entries and the lists of entries. *)
Definition pre_term_rect'
  (T1 : pre_term -> Type)
  (T2 : list pre_term -> Type)
  (T3 : list pre_term * list pre_term -> Type)
  (T4 : pre_term * (list pre_term * list pre_term) -> Type)
  (T5 : list (pre_term * (list pre_term * list pre_term)) -> Type)
  (H1 : forall o, T1 (PT0 o))
  (H2 : forall o t1, T1 t1 -> T1 (PT1 o t1))
  (H3 : forall o t1, T1 t1 -> forall t2, T1 t2 -> T1 (PT2 o t1 t2))
  (HM : forall ps, T2 ps -> forall ns, T2 ns -> T1 (PTMul ps ns))
  (HD : forall l, T5 l -> T1 (PTDH l))
  (H2n : T2 [::])
  (H2c : forall t, T1 t -> forall ts, T2 ts -> T2 (t :: ts))
  (H3p : forall ps, T2 ps -> forall ns, T2 ns -> T3 (ps, ns))
  (H4p : forall b, T1 b -> forall A, T3 A -> T4 (b, A))
  (H5n : T5 [::])
  (H5c : forall e, T4 e -> forall l, T5 l -> T5 (e :: l)) :=
  fix loop1 t {struct t} : T1 t :=
    let fix loop2 ts {struct ts} : T2 ts :=
      match ts with
      | [::] => H2n
      | t :: ts => H2c t (loop1 t) ts (loop2 ts)
      end in
    let loop3 A : T3 A :=
      let: (ps, ns) as A := A return T3 A in H3p ps (loop2 ps) ns (loop2 ns) in
    let loop4 e : T4 e :=
      let: (b, A) as e := e return T4 e in H4p b (loop1 b) A (loop3 A) in
    let fix loop5 l {struct l} : T5 l :=
      match l with
      | [::] => H5n
      | e :: l => H5c e (loop4 e) l (loop5 l)
      end in
    match t with
    | PT0 o => H1 o
    | PT1 o t => H2 o t (loop1 t)
    | PT2 o t1 t2 => H3 o t1 (loop1 t1) t2 (loop1 t2)
    | PTMul ps ns => HM ps (loop2 ps) ns (loop2 ns)
    | PTDH l => HD l (loop5 l)
    end.

Definition list_pre_term_rect' T1 T2 T3 T4 T5 H1 H2 H3 HM HD
  H2n H2c H3p H4p H5n H5c :=
  fix loop2 ts {struct ts} : T2 ts :=
    match ts with
    | [::] => H2n
    | t :: ts =>
      H2c t (@pre_term_rect' T1 T2 T3 T4 T5 H1 H2 H3 HM HD
               H2n H2c H3p H4p H5n H5c t) ts (loop2 ts)
    end.

Definition log_pre_term_rect' T1 T2 (T3 : list pre_term * list pre_term -> Type)
  T4 T5 H1 H2 H3 HM HD H2n H2c (H3p : forall ps, T2 ps -> forall ns, T2 ns ->
  T3 (ps, ns)) H4p H5n H5c A : T3 A :=
  let: (ps, ns) as A := A return T3 A in
  H3p ps (@list_pre_term_rect' T1 T2 T3 T4 T5 H1 H2 H3 HM HD
            H2n H2c H3p H4p H5n H5c ps)
      ns (@list_pre_term_rect' T1 T2 T3 T4 T5 H1 H2 H3 HM HD
            H2n H2c H3p H4p H5n H5c ns).

Definition entry_pre_term_rect' T1 T2 T3
  (T4 : pre_term * (list pre_term * list pre_term) -> Type) T5
  H1 H2 H3 HM HD H2n H2c H3p
  (H4p : forall b, T1 b -> forall A, T3 A -> T4 (b, A)) H5n H5c e : T4 e :=
  let: (b, A) as e := e return T4 e in
  H4p b (@pre_term_rect' T1 T2 T3 T4 T5 H1 H2 H3 HM HD
           H2n H2c H3p H4p H5n H5c b)
      A (@log_pre_term_rect' T1 T2 T3 T4 T5 H1 H2 H3 HM HD
           H2n H2c H3p H4p H5n H5c A).

Definition entries_pre_term_rect' T1 T2 T3 T4 T5 H1 H2 H3 HM HD
  H2n H2c H3p H4p H5n H5c :=
  fix loop5 l {struct l} : T5 l :=
    match l with
    | [::] => H5n
    | e :: l =>
      H5c e (@entry_pre_term_rect' T1 T2 T3 T4 T5 H1 H2 H3 HM HD
               H2n H2c H3p H4p H5n H5c e) l (loop5 l)
    end.

Combined Scheme pre_term_all_rect
  from pre_term_rect', list_pre_term_rect', log_pre_term_rect',
       entry_pre_term_rect', entries_pre_term_rect'.

Definition pre_term_all_indDef := [indDef for pre_term_all_rect].
Canonical pre_term_indType := IndType pre_term pre_term_all_indDef.
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
  (HM : forall ps, foldr (fun t R => T t * R)%type unit ps ->
          forall ns, foldr (fun t R => T t * R)%type unit ns ->
          T (PTMul ps ns))
  (HD : forall l,
          foldr (fun e R =>
                   T e.1 * foldr (fun t R => T t * R)%type unit e.2.1
                   * foldr (fun t R => T t * R)%type unit e.2.2 * R)%type
            unit l ->
          T (PTDH l)) t : T t.
Proof.
pose T2 := foldr (fun t R => T t * R)%type unit.
exact: (@pre_term_rect' T T2 (fun A => T2 A.1 * T2 A.2)%type
          (fun e => T e.1 * T2 e.2.1 * T2 e.2.2)%type
          (foldr (fun e R => T e.1 * T2 e.2.1 * T2 e.2.2 * R)%type unit)
          H1 H2 H3 HM HD tt (fun t Ht ts Hts => (Ht, Hts))
          (fun ps Hps ns Hns => (Hps, Hns))
          (fun b Hb A HA => (Hb, HA.1, HA.2)) tt
          (fun e He l Hl => (He, Hl)) t).
Defined.

Register Scheme pre_term_rect as rect_dep for pre_term.

Definition pre_term_ind (T : pre_term -> Prop) :=
  @pre_term_rect T.

Register Scheme pre_term_ind as ind_dep for pre_term.

Definition seq_pre_term := seq pre_term.
Definition seq_pre_term_isOrder := [derive isOrder for seq pre_term].
HB.instance Definition _ := seq_pre_term_isOrder.

Definition cons_num pt : Z :=
  match pt with
  | PT0 _ => TOp0_tag
  | PT1 _ _ => TOp1_tag
  | PT2 _ _ _ => TOp2_tag
  | PTMul _ _ => TMul_tag
  | PTDH _ => TDH_tag
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

Lemma seqE (ts1 ts2 : seq pre_term) :
  ((ts1 : seqlexi_with Order.default_display _) <= ts2)%O =
  ((ts1 : seq_pre_term) <= ts2)%O.
Proof.
elim: ts1 ts2 => [|t1 ts1 IH] [|t2 ts2] //=.
rewrite [LHS](_ : _ = if t1 == t2 then if ts1 == ts2 then true
                                       else ((ts1 : seq_pre_term) <= ts2)%O
                      else (t1 <= t2)%O) //.
rewrite lexi_cons IH.
case: ltgtP => //= _; exact: le_alt.
Qed.

(** The derived order on the entries of a Diffie-Hellman term: lexicographic,
    comparing the bases, then the positive and the negative exponents. *)
Fixpoint entries_le (l1 l2 : seq (pre_term * (seq pre_term * seq pre_term)))
    : bool :=
  match l1, l2 with
  | [::], _ => true
  | _ :: _, [::] => false
  | (b1, (p1, n1)) :: l1, (b2, (p2, n2)) :: l2 =>
    if b1 == b2 then
      if p1 == p2 then
        if n1 == n2 then entries_le l1 l2
        else ((n1 : seqlexi_with Order.default_display _) <= n2)%O
      else ((p1 : seqlexi_with Order.default_display _) <= p2)%O
    else (b1 <= b2)%O
  end.

Lemma entries_leE l1 l2 : (PTDH l1 <= PTDH l2)%O = entries_le l1 l2.
Proof.
elim: l1 l2 => [|[b1 [p1 n1]] l1 IH] [|[b2 [p2 n2]] l2] //.
have -> : (PTDH ((b1, (p1, n1)) :: l1) <= PTDH ((b2, (p2, n2)) :: l2))%O =
  if ((b1, (p1, n1)) :: l1) == ((b2, (p2, n2)) :: l2) then true else
  if (b1, (p1, n1)) == (b2, (p2, n2)) then (PTDH l1 <= PTDH l2)%O
  else if b1 == b2 then
    (if (p1, n1) == (p2, n2) then true else
     if p1 == p2 then
       (if n1 == n2 then true else ((n1 : seq_pre_term) <= n2)%O)
     else ((p1 : seq_pre_term) <= p2)%O)
  else (b1 <= b2)%O by [].
rewrite /= !seqE.
case: eqP => [[<- <- <- <-]|ne].
  by rewrite !eqxx -IH lexx.
case: eqP => [[<- <- <-]|ne1]; first by rewrite !eqxx IH.
case: (b1 =P b2) => [eb|//]; subst b2.
case: ((p1, n1) =P (p2, n2)) => [[ep en]|nA]; first by subst; case: ne1.
case: (p1 =P p2) => [ep|//]; subst p2.
by case: (n1 =P n2) => [en|//]; subst n2; case: nA.
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
    | PTMul ps1 ns1, PTMul ps2 ns2 =>
      if ps1 == ps2 then
        ((ns1 : seqlexi_with Order.default_display _) <= ns2)%O
      else ((ps1 : seqlexi_with Order.default_display _) <= ps2)%O
    | PTDH l1, PTDH l2 => entries_le l1 l2
    | _, _ => false
    end
  else (cons_num pt1 <=? cons_num pt2)%Z.
Proof.
case: pt1 pt2
    => [o1|o1 t1|o1 t11 t12|ps1 ns1|l1]
       [o2|o2 t2|o2 t21 t22|ps2 ns2|l2] //=.
- by rewrite [RHS]le_alt.
- by rewrite [(t1 <= t2)%O]le_alt.
- by rewrite (le_alt t12).
- by rewrite !seqE [(ns1 : seq_pre_term) <= ns2]le_alt.
- exact: entries_leE.
Qed.

Close Scope order_scope.

Module Exports.
HB.reexport.
End Exports.

End PreTerm.

Export PreTerm.Exports.
