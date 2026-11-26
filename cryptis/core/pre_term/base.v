From cryptis Require Export mathcomp_compat.
From HB Require Import structures.
From mathcomp Require Import order boot.
From deriving Require Import deriving.
From Stdlib Require Import ZArith.ZArith Lia Utf8.
From Stdlib Require List.
Import List (Forall, Forall_inv, Forall_inv_tail, Forall_impl, Forall_forall).
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
Abbreviation TMod_tag := 3%Z.
Abbreviation TDH_tag := 4%Z.

Module PreTerm.

(** [PTMod f] is an exponent: a rational function whose numerator and
    denominator are given by the lists of their positive and negative
    monomials, each monomial a list of atoms.  [PTDH l] is a Diffie-Hellman
    term: [l] maps each base to its logarithm, an exponent given in the same
    way. *)
Unset Elimination Schemes.
Inductive pre_term :=
| PT0 of term_op0
| PT1 of term_op1 & pre_term
| PT2 of term_op2 & pre_term & pre_term
| PTMod of (list (list pre_term) * list (list pre_term)) *
           (list (list pre_term) * list (list pre_term))
| PTDH of list (pre_term * ((list (list pre_term) * list (list pre_term)) *
                            (list (list pre_term) * list (list pre_term)))).
Set Elimination Schemes.

Abbreviation monos := (list (list pre_term)).
Abbreviation poly_lists := (list (list pre_term) * list (list pre_term))%type.
Abbreviation frac_lists := (poly_lists * poly_lists)%type.
Abbreviation entry := (pre_term * frac_lists)%type.

(* [deriving] treats the nested types as further sorts of a mutual family:
   monomials, lists of monomials, polynomials, fractions, entries and lists of
   entries.  The hypotheses are parameters rather than section variables,
   which would get implicit arguments and break [indDef]. *)
Definition pre_term_rect'
  (T1 : pre_term -> Type) (T2 : list pre_term -> Type) (T3 : monos -> Type)
  (T4 : poly_lists -> Type) (T5 : frac_lists -> Type) (T6 : entry -> Type)
  (T7 : list entry -> Type)
  (H1 : forall o, T1 (PT0 o))
  (H2 : forall o t1, T1 t1 -> T1 (PT1 o t1))
  (H3 : forall o t1, T1 t1 -> forall t2, T1 t2 -> T1 (PT2 o t1 t2))
  (HM : forall f, T5 f -> T1 (PTMod f))
  (HD : forall l, T7 l -> T1 (PTDH l))
  (H2n : T2 [::])
  (H2c : forall t, T1 t -> forall ts, T2 ts -> T2 (t :: ts))
  (H3n : T3 [::])
  (H3c : forall m, T2 m -> forall ms, T3 ms -> T3 (m :: ms))
  (H4p : forall ps, T3 ps -> forall ns, T3 ns -> T4 (ps, ns))
  (H5p : forall n, T4 n -> forall d, T4 d -> T5 (n, d))
  (H6p : forall b, T1 b -> forall f, T5 f -> T6 (b, f))
  (H7n : T7 [::])
  (H7c : forall e, T6 e -> forall l, T7 l -> T7 (e :: l)) :=
  fix loop1 t {struct t} : T1 t :=
    let fix loop2 ts {struct ts} : T2 ts :=
      match ts with
      | [::] => H2n
      | t :: ts => H2c t (loop1 t) ts (loop2 ts)
      end in
    let fix loop3 ms {struct ms} : T3 ms :=
      match ms with
      | [::] => H3n
      | m :: ms => H3c m (loop2 m) ms (loop3 ms)
      end in
    let loop4 A : T4 A :=
      let: (ps, ns) as A := A return T4 A in H4p ps (loop3 ps) ns (loop3 ns) in
    let loop5 F : T5 F :=
      let: (n, d) as F := F return T5 F in H5p n (loop4 n) d (loop4 d) in
    let loop6 e : T6 e :=
      let: (b, F) as e := e return T6 e in H6p b (loop1 b) F (loop5 F) in
    let fix loop7 l {struct l} : T7 l :=
      match l with
      | [::] => H7n
      | e :: l => H7c e (loop6 e) l (loop7 l)
      end in
    match t with
    | PT0 o => H1 o
    | PT1 o t => H2 o t (loop1 t)
    | PT2 o t1 t2 => H3 o t1 (loop1 t1) t2 (loop1 t2)
    | PTMod f => HM f (loop5 f)
    | PTDH l => HD l (loop7 l)
    end.

Definition mono_pre_term_rect' T1 T2 T3 T4 T5 T6 T7 H1 H2 H3 HM HD
  H2n H2c H3n H3c H4p H5p H6p H7n H7c :=
  fix loop2 ts {struct ts} : T2 ts :=
    match ts with
    | [::] => H2n
    | t :: ts =>
      H2c t (@pre_term_rect' T1 T2 T3 T4 T5 T6 T7 H1 H2 H3 HM HD
               H2n H2c H3n H3c H4p H5p H6p H7n H7c t) ts (loop2 ts)
    end.

Definition monos_pre_term_rect' T1 T2 T3 T4 T5 T6 T7 H1 H2 H3 HM HD
  H2n H2c H3n H3c H4p H5p H6p H7n H7c :=
  fix loop3 ms {struct ms} : T3 ms :=
    match ms with
    | [::] => H3n
    | m :: ms =>
      H3c m (@mono_pre_term_rect' T1 T2 T3 T4 T5 T6 T7 H1 H2 H3 HM HD
               H2n H2c H3n H3c H4p H5p H6p H7n H7c m) ms (loop3 ms)
    end.

Definition poly_pre_term_rect' T1 T2 T3 (T4 : poly_lists -> Type) T5 T6 T7
  H1 H2 H3 HM HD H2n H2c H3n H3c
  (H4p : forall ps, T3 ps -> forall ns, T3 ns -> T4 (ps, ns))
  H5p H6p H7n H7c A : T4 A :=
  let: (ps, ns) as A := A return T4 A in
  H4p ps (@monos_pre_term_rect' T1 T2 T3 T4 T5 T6 T7 H1 H2 H3 HM HD
            H2n H2c H3n H3c H4p H5p H6p H7n H7c ps)
      ns (@monos_pre_term_rect' T1 T2 T3 T4 T5 T6 T7 H1 H2 H3 HM HD
            H2n H2c H3n H3c H4p H5p H6p H7n H7c ns).

Definition frac_pre_term_rect' T1 T2 T3 T4 (T5 : frac_lists -> Type) T6 T7
  H1 H2 H3 HM HD H2n H2c H3n H3c H4p
  (H5p : forall n, T4 n -> forall d, T4 d -> T5 (n, d))
  H6p H7n H7c F : T5 F :=
  let: (n, d) as F := F return T5 F in
  H5p n (@poly_pre_term_rect' T1 T2 T3 T4 T5 T6 T7 H1 H2 H3 HM HD
           H2n H2c H3n H3c H4p H5p H6p H7n H7c n)
      d (@poly_pre_term_rect' T1 T2 T3 T4 T5 T6 T7 H1 H2 H3 HM HD
           H2n H2c H3n H3c H4p H5p H6p H7n H7c d).

Definition entry_pre_term_rect' T1 T2 T3 T4 T5 (T6 : entry -> Type) T7
  H1 H2 H3 HM HD H2n H2c H3n H3c H4p H5p
  (H6p : forall b, T1 b -> forall f, T5 f -> T6 (b, f)) H7n H7c e : T6 e :=
  let: (b, F) as e := e return T6 e in
  H6p b (@pre_term_rect' T1 T2 T3 T4 T5 T6 T7 H1 H2 H3 HM HD
           H2n H2c H3n H3c H4p H5p H6p H7n H7c b)
      F (@frac_pre_term_rect' T1 T2 T3 T4 T5 T6 T7 H1 H2 H3 HM HD
           H2n H2c H3n H3c H4p H5p H6p H7n H7c F).

Definition entries_pre_term_rect' T1 T2 T3 T4 T5 T6 T7 H1 H2 H3 HM HD
  H2n H2c H3n H3c H4p H5p H6p H7n H7c :=
  fix loop7 l {struct l} : T7 l :=
    match l with
    | [::] => H7n
    | e :: l =>
      H7c e (@entry_pre_term_rect' T1 T2 T3 T4 T5 T6 T7 H1 H2 H3 HM HD
               H2n H2c H3n H3c H4p H5p H6p H7n H7c e) l (loop7 l)
    end.

Combined Scheme pre_term_all_rect
  from pre_term_rect', mono_pre_term_rect', monos_pre_term_rect',
       poly_pre_term_rect', frac_pre_term_rect', entry_pre_term_rect',
       entries_pre_term_rect'.

(* Simplifying or computing with instances derived for a type this large
   stalls, so they are not reduced ([nored]), and the order is written by
   hand ([pt_cmp] below), so that programs can compute it. *)
Definition pre_term_all_indDef := [indDef for pre_term_all_rect].
Canonical pre_term_indType := IndType pre_term pre_term_all_indDef.
Definition pre_term_hasDecEq := [derive nored hasDecEq for pre_term].
#[export] HB.instance Definition _ := pre_term_hasDecEq.
Definition pre_term_hasChoice := [derive hasChoice for pre_term].
#[export] HB.instance Definition _ := pre_term_hasChoice.
Definition pre_term_isCountable := [derive isCountable for pre_term].
#[export] HB.instance Definition _ := pre_term_isCountable.

(** Induction hypotheses for the atoms of nested lists. *)
Definition list_all (T : pre_term -> Type) (ts : list pre_term) : Type :=
  foldr (fun t R => T t * R)%type unit ts.

Definition monos_all (T : pre_term -> Type) (ms : monos) : Type :=
  foldr (fun m R => list_all T m * R)%type unit ms.

Definition poly_all (T : pre_term -> Type) (A : poly_lists) : Type :=
  (monos_all T A.1 * monos_all T A.2)%type.

Definition frac_all (T : pre_term -> Type) (F : frac_lists) : Type :=
  (poly_all T F.1 * poly_all T F.2)%type.

Definition entries_all (T : pre_term -> Type) (l : list entry) : Type :=
  foldr (fun e R => T e.1 * frac_all T e.2 * R)%type unit l.

Definition pre_term_rect (T : pre_term -> Type)
  (H1 : forall o, T (PT0 o))
  (H2 : forall o t1, T t1 -> T (PT1 o t1))
  (H3 : forall o t1, T t1 -> forall t2, T t2 -> T (PT2 o t1 t2))
  (HM : forall f, frac_all T f -> T (PTMod f))
  (HD : forall l, entries_all T l -> T (PTDH l)) t : T t.
Proof.
exact: (@pre_term_rect' T (list_all T) (monos_all T) (poly_all T)
          (frac_all T) (fun e => T e.1 * frac_all T e.2)%type
          (entries_all T)
          H1 H2 H3 HM HD tt (fun t Ht ts Hts => (Ht, Hts))
          tt (fun m Hm ms Hms => (Hm, Hms))
          (fun ps Hps ns Hns => (Hps, Hns))
          (fun n Hn d Hd => (Hn, Hd))
          (fun b Hb F HF => (Hb, HF)) tt
          (fun e He l Hl => (He, Hl)) t).
Defined.

Register Scheme pre_term_rect as rect_dep for pre_term.

Definition pre_term_ind (T : pre_term -> Prop) :=
  @pre_term_rect T.

Register Scheme pre_term_ind as ind_dep for pre_term.

(** ** Order

    Pre-terms are compared by constructor, and then by their arguments,
    lexicographically ([pt_cmp]).  Lists are compared lexicographically, the
    shorter prefix first ([cmp_list]), and pairs component-wise ([cmp_pair]).
    [pt_cmp] is a strict total order ([pt_cmp_eq], [pt_cmp_opp],
    [pt_cmp_trans]), and [x <= y] is [pt_cmp x y != Gt]. *)

Section Cmp.

Context {A B : Type}.

Definition cmp_list (c : A → A → comparison) : list A → list A → comparison :=
  fix go xs ys :=
    match xs, ys with
    | [::], [::] => Eq
    | [::], _ :: _ => Lt
    | _ :: _, [::] => Gt
    | x :: xs, y :: ys => match c x y with Eq => go xs ys | r => r end
    end.

Definition cmp_pair (ca : A → A → comparison) (cb : B → B → comparison)
    (p q : A * B) : comparison :=
  let: (a1, b1) := p in let: (a2, b2) := q in
  match ca a1 a2 with Eq => cb b1 b2 | r => r end.

End Cmp.

Definition cmp_ord {d} {T : orderType d} (x y : T) : comparison :=
  if x == y then Eq else if (x <= y)%O then Lt else Gt.

Definition cmp_poly (c : pre_term → pre_term → comparison) :=
  cmp_pair (cmp_list (cmp_list c)) (cmp_list (cmp_list c)).

Definition cmp_frac (c : pre_term → pre_term → comparison) :=
  cmp_pair (cmp_poly c) (cmp_poly c).

Fixpoint pt_cmp (x y : pre_term) {struct x} : comparison :=
  match x, y with
  | PT0 o1, PT0 o2 => cmp_ord o1 o2
  | PT0 _, _ => Lt
  | _, PT0 _ => Gt
  | PT1 o1 t1, PT1 o2 t2 =>
    match cmp_ord o1 o2 with Eq => pt_cmp t1 t2 | r => r end
  | PT1 _ _, _ => Lt
  | _, PT1 _ _ => Gt
  | PT2 o1 a1 b1, PT2 o2 a2 b2 =>
    match cmp_ord o1 o2 with
    | Eq => match pt_cmp a1 a2 with Eq => pt_cmp b1 b2 | r => r end
    | r => r
    end
  | PT2 _ _ _, _ => Lt
  | _, PT2 _ _ _ => Gt
  | PTMod f1, PTMod f2 => cmp_frac pt_cmp f1 f2
  | PTMod _, _ => Lt
  | _, PTMod _ => Gt
  | PTDH l1, PTDH l2 => cmp_list (cmp_pair pt_cmp (cmp_frac pt_cmp)) l1 l2
  end.

Section CmpLaws.

Context {A B : Type}.
Implicit Types (ca : A → A → comparison) (cb : B → B → comparison).

Lemma cmp_list_eq ca xs :
  Forall (λ x, ∀ y, ca x y = Eq ↔ x = y) xs →
  ∀ ys, cmp_list ca xs ys = Eq ↔ xs = ys.
Proof.
elim: xs => [|x xs IH] H [|y ys] //=.
have Hx := Forall_inv H; have {}IH := IH (Forall_inv_tail H).
case E: (ca x y); split=> // e.
- by move/Hx: E => ->; rewrite (proj1 (IH ys) e).
- by injection e as ex exs; apply/IH.
- by injection e as ex exs; move: E; rewrite (proj2 (Hx y) ex).
- by injection e as ex exs; move: E; rewrite (proj2 (Hx y) ex).
Qed.

Lemma cmp_list_opp ca xs :
  Forall (λ x, ∀ y, ca y x = CompOpp (ca x y)) xs →
  ∀ ys, cmp_list ca ys xs = CompOpp (cmp_list ca xs ys).
Proof.
elim: xs => [|x xs IH] H [|y ys] //=.
rewrite (Forall_inv H y).
by case: (ca x y) => //=; exact: IH (Forall_inv_tail H) ys.
Qed.

Lemma cmp_list_trans ca :
  (∀ x y, ca x y = Eq → x = y) →
  ∀ xs, Forall (λ x, ∀ y z, ca x y = Lt → ca y z = Lt → ca x z = Lt) xs →
  ∀ ys zs, cmp_list ca xs ys = Lt → cmp_list ca ys zs = Lt →
  cmp_list ca xs zs = Lt.
Proof.
move=> Heq; elim=> [|x xs IH] H [|y ys] [|z zs] //=.
have Hx := Forall_inv H; have {}IH := IH (Forall_inv_tail H).
case Exy: (ca x y) => //; case Eyz: (ca y z) => //.
- by move/Heq: Exy => ->; rewrite Eyz; exact: IH.
- by move/Heq: Exy => ->; rewrite Eyz.
- by move/Heq: Eyz => <-; rewrite Exy.
- by rewrite (Hx _ _ Exy Eyz).
Qed.

Lemma cmp_pair_eq ca cb a b :
  (∀ a', ca a a' = Eq ↔ a = a') → (∀ b', cb b b' = Eq ↔ b = b') →
  ∀ q, cmp_pair ca cb (a, b) q = Eq ↔ (a, b) = q.
Proof.
move=> Ha Hb [a' b'] /=.
case E: (ca a a'); split=> // e.
- by move/Ha: E => ->; rewrite (proj1 (Hb b') e).
- by injection e as ea eb; apply/Hb.
- by injection e as ea eb; move: E; rewrite (proj2 (Ha a') ea).
- by injection e as ea eb; move: E; rewrite (proj2 (Ha a') ea).
Qed.

Lemma cmp_pair_opp ca cb a b :
  (∀ a', ca a' a = CompOpp (ca a a')) → (∀ b', cb b' b = CompOpp (cb b b')) →
  ∀ q, cmp_pair ca cb q (a, b) = CompOpp (cmp_pair ca cb (a, b) q).
Proof. by move=> Ha Hb [a' b'] /=; rewrite Ha Hb; case: (ca a a'). Qed.

Lemma cmp_pair_trans ca cb :
  (∀ x y, ca x y = Eq → x = y) → (∀ x y, cb x y = Eq → x = y) →
  ∀ a b,
  (∀ a' a'', ca a a' = Lt → ca a' a'' = Lt → ca a a'' = Lt) →
  (∀ b' b'', cb b b' = Lt → cb b' b'' = Lt → cb b b'' = Lt) →
  ∀ q r, cmp_pair ca cb (a, b) q = Lt → cmp_pair ca cb q r = Lt →
  cmp_pair ca cb (a, b) r = Lt.
Proof.
move=> Hea Heb a b Ha Hb [a' b'] [a'' b''] /=.
case E1: (ca a a') => //; case E2: (ca a' a'') => //.
- by move/Hea: E1 => ->; rewrite E2; exact: Hb.
- by move/Hea: E1 => ->; rewrite E2.
- by move/Hea: E2 => <-; rewrite E1.
- by rewrite (Ha _ _ E1 E2).
Qed.

End CmpLaws.

Section OrdLaws.

Context {d} {T : orderType d}.
Implicit Types x y z : T.

Lemma cmp_ord_eq x y : cmp_ord x y = Eq ↔ x = y.
Proof.
rewrite /cmp_ord; case: eqP => [e|ne]; first by split.
by case: (x <= y)%O; split=> // e; case: ne.
Qed.

Lemma cmp_ord_opp x y : cmp_ord y x = CompOpp (cmp_ord x y).
Proof.
rewrite /cmp_ord eq_sym; case: eqP => [_|ne] //=.
case: (leP x y) => [le|lt] /=.
  by rewrite leNgt lt_neqAle le andbT; move/eqP: ne => ->.
by rewrite (ltW lt).
Qed.

Lemma cmp_ord_trans x y z :
  cmp_ord x y = Lt → cmp_ord y z = Lt → cmp_ord x z = Lt.
Proof.
rewrite /cmp_ord.
case: eqP => // nxy; case: ifP => // lxy _.
case: eqP => // nyz; case: ifP => // lyz _.
have ltxy : (x < y)%O by rewrite lt_neqAle lxy andbT; apply/eqP.
have ltxz : (x < z)%O := lt_le_trans ltxy lyz.
by rewrite (ltW ltxz) (lt_eqF ltxz).
Qed.

End OrdLaws.

Section PtCmpLaws.

Implicit Types (x y z : pre_term) (c : pre_term → pre_term → comparison).

Lemma list_all_Forall (P : pre_term → Prop) l : list_all P l → Forall P l.
Proof. by elim: l => [|x l IH] /= => [_|[Px /IH]]; constructor. Qed.

Lemma monos_all_Forall_impl (P : pre_term → Prop) (Q : list pre_term → Prop) ms
  :
  (∀ m, Forall P m → Q m) → monos_all P ms → Forall Q ms.
Proof.
move=> PQ; elim: ms => [|m ms IH] /= => [_|[/list_all_Forall Pm /IH]].
  by constructor.
by constructor; [exact: PQ|].
Qed.

Lemma entries_all_Forall_impl (P : pre_term → Prop) (Q : frac_lists → Prop) l :
  (∀ F, frac_all P F → Q F) → entries_all P l → Forall (λ e, P e.1 ∧ Q e.2) l.
Proof.
move=> PQ; elim: l => [|e l IH] /= => [_|[[Pb Pf] /IH Hl]].
  by constructor.
by constructor => //; split=> //; exact: PQ.
Qed.

Lemma monos_all_Forall (P : pre_term → Prop) ms :
  monos_all P ms → Forall (Forall P) ms.
Proof. exact: monos_all_Forall_impl. Qed.

Lemma entries_all_Forall (P : pre_term → Prop) l :
  entries_all P l → Forall (λ e, P e.1 ∧ inhabited (frac_all P e.2)) l.
Proof.
elim: l => [|e l IH] /= => [_|[[Pb Pf] /IH Hl]]; constructor => //.
Qed.

Lemma cmp_frac_eq c F :
  frac_all (λ x, ∀ y, c x y = Eq ↔ x = y) F →
  ∀ F', cmp_frac c F F' = Eq ↔ F = F'.
Proof.
case: F => [[ps ns] [qs rs]] [[Hps Hns] [Hqs Hrs]].
have M ms : monos_all (λ x, ∀ y, c x y = Eq ↔ x = y) ms →
    ∀ ms', cmp_list (cmp_list c) ms ms' = Eq ↔ ms = ms'.
  move=> H; apply: cmp_list_eq; apply: monos_all_Forall_impl H => m Hm.
  exact: cmp_list_eq.
by apply: cmp_pair_eq; apply: cmp_pair_eq; apply: M.
Qed.

Lemma cmp_frac_opp c F :
  frac_all (λ x, ∀ y, c y x = CompOpp (c x y)) F →
  ∀ F', cmp_frac c F' F = CompOpp (cmp_frac c F F').
Proof.
case: F => [[ps ns] [qs rs]] [[Hps Hns] [Hqs Hrs]].
have M ms : monos_all (λ x, ∀ y, c y x = CompOpp (c x y)) ms →
    ∀ ms', cmp_list (cmp_list c) ms' ms =
           CompOpp (cmp_list (cmp_list c) ms ms').
  move=> H; apply: cmp_list_opp; apply: monos_all_Forall_impl H => m Hm.
  exact: cmp_list_opp.
by apply: cmp_pair_opp; apply: cmp_pair_opp; apply: M.
Qed.

Lemma pt_cmp_eq x y : pt_cmp x y = Eq ↔ x = y.
Proof.
elim: x y => [o1|o1 t1 IH|o1 a1 IHa b1 IHb|f1 IH|l1 IH]
  [o2|o2 t2|o2 a2 b2|f2|l2] /=; try by split.
- by rewrite cmp_ord_eq; split=> [->|[->]].
- case E: (cmp_ord o1 o2); last 2 first.
  + by split=> // -[eo _]; move: E; rewrite eo (proj2 (cmp_ord_eq _ _) erefl).
  + by split=> // -[eo _]; move: E; rewrite eo (proj2 (cmp_ord_eq _ _) erefl).
  move/cmp_ord_eq: E => ->; rewrite IH.
  by split=> [->|[->]].
- case E: (cmp_ord o1 o2); last 2 first.
  + by split=> // -[eo _]; move: E; rewrite eo (proj2 (cmp_ord_eq _ _) erefl).
  + by split=> // -[eo _]; move: E; rewrite eo (proj2 (cmp_ord_eq _ _) erefl).
  move/cmp_ord_eq: E => ->.
  case E: (pt_cmp a1 a2); last 2 first.
  + by split=> // -[ea _]; move: E; rewrite (proj2 (IHa _) ea).
  + by split=> // -[ea _]; move: E; rewrite (proj2 (IHa _) ea).
  move/IHa: E => ->; rewrite IHb.
  by split=> [->|[->]].
- rewrite (cmp_frac_eq IH); by split=> [->|[->]].
- have F : Forall (λ e, ∀ e', cmp_pair pt_cmp (cmp_frac pt_cmp) e e' = Eq ↔
                              e = e') l1.
    move: (entries_all_Forall_impl (@cmp_frac_eq pt_cmp) IH).
    by apply: Forall_impl => -[b F] [Hb HF]; apply: cmp_pair_eq.
  by rewrite (cmp_list_eq F); split=> [->|[->]].
Qed.

Lemma pt_cmp_opp x y : pt_cmp y x = CompOpp (pt_cmp x y).
Proof.
elim: x y => [o1|o1 t1 IH|o1 a1 IHa b1 IHb|f1 IH|l1 IH]
  [o2|o2 t2|o2 a2 b2|f2|l2] //=.
- exact: cmp_ord_opp.
- by rewrite cmp_ord_opp; case: (cmp_ord o1 o2) => //=; exact: IH.
- rewrite cmp_ord_opp; case: (cmp_ord o1 o2) => //=.
  by rewrite IHa; case: (pt_cmp a1 a2) => //=; exact: IHb.
- exact: cmp_frac_opp IH f2.
- apply: cmp_list_opp.
  move: (entries_all_Forall_impl (@cmp_frac_opp pt_cmp) IH).
  by apply: Forall_impl => -[b F] [Hb HF]; apply: cmp_pair_opp.
Qed.

Lemma pt_cmp_refl x : pt_cmp x x = Eq.
Proof. exact/pt_cmp_eq. Qed.

Lemma cmp_frac_eq_all c :
  (∀ x y, c x y = Eq ↔ x = y) → ∀ F F', cmp_frac c F F' = Eq ↔ F = F'.
Proof.
move=> Hc.
have E1 m m' : cmp_list c m m' = Eq ↔ m = m'.
  by apply: cmp_list_eq; apply/Forall_forall => x _ y; exact: Hc.
have E2 ms ms' : cmp_list (cmp_list c) ms ms' = Eq ↔ ms = ms'.
  by apply: cmp_list_eq; apply/Forall_forall => m _ m'; exact: E1.
case=> [[ps ns] [qs rs]].
by apply: cmp_pair_eq; apply: cmp_pair_eq; apply: E2.
Qed.

Lemma cmp_frac_trans c F :
  (∀ x y, c x y = Eq ↔ x = y) →
  frac_all (λ x, ∀ y z, c x y = Lt → c y z = Lt → c x z = Lt) F →
  ∀ F' F'', cmp_frac c F F' = Lt → cmp_frac c F' F'' = Lt →
  cmp_frac c F F'' = Lt.
Proof.
move=> Hc; case: F => [[ps ns] [qs rs]] [[Hps Hns] [Hqs Hrs]].
have E1' m m' : cmp_list c m m' = Eq ↔ m = m'.
  by apply: cmp_list_eq; apply/Forall_forall => x _ y; exact: Hc.
have E1 m m' : cmp_list c m m' = Eq → m = m' by move/E1'.
have E2' ms ms' : cmp_list (cmp_list c) ms ms' = Eq ↔ ms = ms'.
  by apply: cmp_list_eq; apply/Forall_forall => m _ m'; exact: E1'.
have E2 ms ms' : cmp_list (cmp_list c) ms ms' = Eq → ms = ms' by move/E2'.
have E3 A A' : cmp_poly c A A' = Eq → A = A'.
  by case: A => ps' ns'; move/(cmp_pair_eq (E2' ps') (E2' ns')).
have M ms : monos_all (λ x, ∀ y z, c x y = Lt → c y z = Lt → c x z = Lt) ms →
    ∀ ms' ms'', cmp_list (cmp_list c) ms ms' = Lt →
    cmp_list (cmp_list c) ms' ms'' = Lt → cmp_list (cmp_list c) ms ms'' = Lt.
  move=> H; apply: (cmp_list_trans E1).
  apply: monos_all_Forall_impl H => m Hm m' m''.
  by apply: (cmp_list_trans _ Hm) => u v /Hc.
have P ps' ns' : monos_all (λ x, ∀ y z, c x y = Lt → c y z = Lt → c x z = Lt)
                   ps' →
    monos_all (λ x, ∀ y z, c x y = Lt → c y z = Lt → c x z = Lt) ns' →
    ∀ A' A'', cmp_poly c (ps', ns') A' = Lt → cmp_poly c A' A'' = Lt →
    cmp_poly c (ps', ns') A'' = Lt.
  by move=> H1 H2; apply: cmp_pair_trans => //; [exact: M|exact: M].
apply: cmp_pair_trans => //; [exact: P|exact: P].
Qed.

Lemma pt_cmp_trans x y z :
  pt_cmp x y = Lt → pt_cmp y z = Lt → pt_cmp x z = Lt.
Proof.
have Eeq u v : pt_cmp u v = Eq → u = v by move/pt_cmp_eq.
have Eord (d : Order.disp_t) (T : orderType d) (u v : T) :
    cmp_ord u v = Eq → u = v.
  by move/cmp_ord_eq.
elim: x y z => [o1|o1 t1 IH|o1 a1 IHa b1 IHb|f1 IH|l1 IH]
  [o2|o2 t2|o2 a2 b2|f2|l2] [o3|o3 t3|o3 a3 b3|f3|l3] //=.
- exact: cmp_ord_trans.
- move=> h1 h2.
  exact: (@cmp_pair_trans _ _ cmp_ord pt_cmp (@Eord _ _) Eeq o1 t1
            (@cmp_ord_trans _ _ o1) IH (o2, t2) (o3, t3) h1 h2).
- move=> h1 h2.
  have Ep (p q : pre_term * pre_term) : cmp_pair pt_cmp pt_cmp p q = Eq →
      p = q.
    by case: p => a b; move/(cmp_pair_eq (@pt_cmp_eq a) (@pt_cmp_eq b)).
  have Tp : ∀ q r, cmp_pair pt_cmp pt_cmp (a1, b1) q = Lt →
      cmp_pair pt_cmp pt_cmp q r = Lt → cmp_pair pt_cmp pt_cmp (a1, b1) r = Lt.
    exact: cmp_pair_trans.
  exact: (@cmp_pair_trans _ _ cmp_ord (cmp_pair pt_cmp pt_cmp) (@Eord _ _) Ep
            o1 (a1, b1) (@cmp_ord_trans _ _ o1) Tp (o2, (a2, b2))
            (o3, (a3, b3)) h1 h2).
- exact: cmp_frac_trans pt_cmp_eq IH f2 f3.
- have EF F F' : cmp_frac pt_cmp F F' = Eq → F = F'.
    by move/(cmp_frac_eq_all pt_cmp_eq).
  have HeqE (e e' : pre_term * frac_lists) :
      cmp_pair pt_cmp (cmp_frac pt_cmp) e e' = Eq → e = e'.
    case: e => b F.
    by move/(cmp_pair_eq (@pt_cmp_eq b) (cmp_frac_eq_all pt_cmp_eq F)).
  apply: (cmp_list_trans HeqE).
  move: (entries_all_Forall_impl
           (fun F => @cmp_frac_trans pt_cmp F pt_cmp_eq) IH).
  apply: Forall_impl => -[b F] [Hb HF] e' e''.
  exact: (cmp_pair_trans Eeq EF Hb HF).
Qed.

End PtCmpLaws.

Definition pt_le (x y : pre_term) : bool :=
  if pt_cmp x y is Gt then false else true.

Lemma pt_le_anti : antisymmetric pt_le.
Proof.
move=> x y /andP []; rewrite /pt_le (pt_cmp_opp x y).
by case E: (pt_cmp x y) => //= _ _; exact/pt_cmp_eq.
Qed.

Lemma pt_le_trans : transitive pt_le.
Proof.
move=> y x z; rewrite /pt_le.
case Exy: (pt_cmp x y) => //; case Eyz: (pt_cmp y z) => //.
- by move/pt_cmp_eq: Exy => ->; rewrite Eyz.
- by move/pt_cmp_eq: Exy => ->; rewrite Eyz.
- by move/pt_cmp_eq: Eyz => <-; rewrite Exy.
- by rewrite (pt_cmp_trans Exy Eyz).
Qed.

Lemma pt_le_total : total pt_le.
Proof. by move=> x y; rewrite /pt_le (pt_cmp_opp x y); case: (pt_cmp x y). Qed.

Definition pre_term_isOrder :=
  @Order.isOrder.Build Order.default_display pre_term pt_le _ _ _
    (fun _ _ => erefl) (fun _ _ => erefl) (fun _ _ => erefl)
    pt_le_anti pt_le_trans pt_le_total.
#[export] HB.instance Definition _ := pre_term_isOrder.

Lemma pt_leE x y : (x <= y)%O = pt_le x y.
Proof. by []. Qed.

Lemma pt_ltE x y : (x < y)%O = if pt_cmp x y is Lt then true else false.
Proof.
rewrite lt_def pt_leE /pt_le.
case E: (pt_cmp x y) => //=; last by rewrite andbF.
- by move/pt_cmp_eq: E => ->; rewrite eqxx.
- by rewrite andbT; apply/eqP => e; move: E; rewrite e pt_cmp_refl.
Qed.

Register Scheme pre_term_ind as ind_dep for pre_term.

Definition cons_num pt : Z :=
  match pt with
  | PT0 _ => TOp0_tag
  | PT1 _ _ => TOp1_tag
  | PT2 _ _ _ => TOp2_tag
  | PTMod _ => TMod_tag
  | PTDH _ => TDH_tag
  end.

Module Exports.
HB.reexport.
End Exports.

End PreTerm.

Export PreTerm.Exports.
