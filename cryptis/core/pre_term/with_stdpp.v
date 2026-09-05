From cryptis Require Import mathcomp_compat lib.
From cryptis.lib Require Import list_sort.
From mathcomp Require Import ssreflect.
From mathcomp Require Import all_order.
From mathcomp Require eqtype ssrbool path.
From deriving Require Import deriving.
From stdpp Require Import gmap sorting lexico.
From iris.heap_lang Require Import notation.
From iris.heap_lang Require Import primitive_laws.
From cryptis.core.pre_term Require Import base.

Canonical term_op0O := leibnizO term_op0.

#[global]
Instance term_op0_eq_dec : EqDecision term_op0.
Proof. exact: def_eq_decision. Defined.

#[global]
Instance repr_term_op0 : Repr term_op0 := λ o,
  match o with
  | O0Int n => (#TInt_tag, #n)%V
  | O0Nonce a => (#TNonce_tag, #(nonce_loc a))%V
  end.

Definition int_of_key_type kt : Z :=
  match kt with
  | AEnc => 0
  | ADec => 1
  | Sign => 2
  | Verify => 3
  | SEnc => 4
  end.

Definition key_type_of_int (n : Z) :=
  match n with
  | 0%Z => AEnc
  | 1%Z => ADec
  | 2%Z => Sign
  | 3%Z => Verify
  | _ => SEnc
  end.

Canonical key_typeO := leibnizO key_type.

#[global]
Instance key_type_eq_dec : EqDecision key_type.
Proof. exact: def_eq_decision. Defined.

#[global]
Instance int_of_key_typeK : Cancel (=) key_type_of_int int_of_key_type.
Proof. by case. Qed.

#[global]
Instance int_of_key_type_inj : Inj (=) (=) int_of_key_type.
Proof. by apply (@cancel_inj _ _ _ key_type_of_int); apply _. Qed.

#[global]
Instance int_of_key_type_countable : Countable key_type.
Proof. apply (inj_countable' _ _ int_of_key_typeK). Qed.

#[global]
Instance repr_key_type : Repr key_type := λ kt, #(int_of_key_type kt).

Canonical term_op1O := leibnizO term_op1.

#[global]
Instance term_op1_eq_dec : EqDecision term_op1.
Proof. exact: def_eq_decision. Defined.

Instance repr_term_op1 : Repr term_op1 := λ o,
  match o with
  | O1Key kt => (#TKey_tag, repr kt)%V
  | O1Hash => (#THash_tag, #())%V
  | O1Inv => (#TInv_tag, #())%V
  end.

Canonical term_op2O := leibnizO term_op2.

#[global]
Instance term_op2_eq_dec : EqDecision term_op2.
Proof. exact: def_eq_decision. Defined.

Instance repr_term_op2 : Repr term_op2 := λ o,
  match o with
  | O2Pair => #TPair_tag
  | O2Seal => #TSeal_tag
  | O2Exp => #TExp_tag
  end.

Section ValOfPreTerm.

Import PreTerm.

Definition val_of_pre_term : Repr pre_term := fix val_of_pre_term pt :=
  match pt with
  | PT0 o =>
    (#TOp0_tag, repr o)%V
  | PT1 o t =>
    (#TOp1_tag, (repr o, val_of_pre_term t))%V
  | PT2 o t1 t2 =>
    (#TOp2_tag, (repr o, val_of_pre_term t1, val_of_pre_term t2))%V
  | PTMul ts =>
    (#TMul_tag, repr_list (map val_of_pre_term ts))%V
  end.

Global Existing Instance val_of_pre_term.

End ValOfPreTerm.

Definition nonce_eq_dec : EqDecision nonce := Eval hnf in def_eq_decision _.
Global Existing Instance nonce_eq_dec.
Global Instance nonce_countable : Countable nonce.
Proof. exact: def_countable. Qed.

Definition nonces_of_term_op0 o : gset nonce :=
  match o with
  | O0Int _ => ∅
  | O0Nonce a => {[a]}
  end.

Fixpoint nonces_of_pre_term pt : gset nonce :=
  match pt with
  | PreTerm.PT0 o => nonces_of_term_op0 o
  | PreTerm.PT1 _ t => nonces_of_pre_term t
  | PreTerm.PT2 _ t1 t2 => nonces_of_pre_term t1 ∪ nonces_of_pre_term t2
  | PreTerm.PTMul ts => ⋃ map nonces_of_pre_term ts
  end.

Global Instance pre_term_inhabited : Inhabited PreTerm.pre_term.
Proof. exact: (populate (PreTerm.PT0 (O0Int 0))). Qed.

Definition pre_term_eq_dec : EqDecision PreTerm.pre_term :=
  Eval hnf in def_eq_decision _.
Global Existing Instance pre_term_eq_dec.

Global Instance pre_term_countable : Countable PreTerm.pre_term :=
  def_countable _ pre_term_eq_dec.

(** stdpp typeclass wrappers around the ssreflect total order on pre-terms
    defined in [base.v], so that stdpp's [merge_sort] and [StronglySorted] can be
    used to canonicalise products. *)
Section PreTermOrder.
Import Order.POrderTheory Order.TotalTheory ssrbool.
Open Scope order_scope.

(* We spell out [is_true] so that this order relation lands on ssreflect's
   boolean coercion (matching the mathcomp order lemmas) rather than stdpp's
   [Is_true]. *)
Definition pt_order : relation PreTerm.pre_term := fun x y => is_true (x <= y).

Global Instance pt_order_dec : RelDecision pt_order.
Proof. rewrite /pt_order /RelDecision => x y; case: (x <= y); [by left | by right]. Qed.

Global Instance pt_order_refl : Reflexive pt_order.
Proof. move=> x; exact: lexx. Qed.

Global Instance pt_order_trans : Transitive pt_order.
Proof. move=> x y z; exact: le_trans. Qed.

Global Instance pt_order_total : Total pt_order.
Proof. by move=> x y; case/orP: (le_total x y); [left|right]. Qed.

Global Instance pt_order_antisymm : AntiSymm eq pt_order.
Proof. move=> x y Hxy Hyx; apply: le_anti; apply/andP; by split. Qed.

End PreTermOrder.

(** stdpp [Lexico] packaging of the same derived order.  [lib/list.v] states the
    HeapLang comparison spec [twp_leq_list] with stdpp's strict [lexico], so
    the [PTMul] case of the pre-term comparison needs the derived order exposed
    under that class.  Since the derived order on [PTMul ts] is
    mathcomp's lexicographic order on [ts] ([base.leqE]), and stdpp's
    [list_lexico] is the lexicographic order built from [lexico] on the
    elements, the two agree — that is [pt_order_mul] below. *)
Section PreTermLexico.
#[warnings="-ambiguous-paths"]
Import Order.POrderTheory Order.TotalTheory ssrbool boot.eqtype.
Open Scope order_scope.

(* As with [pt_order], [is_true] is spelled out so the relation lands on
   ssreflect's boolean coercion rather than stdpp's [Is_true]. *)
Global Instance pre_term_lexico : Lexico PreTerm.pre_term :=
  fun x y => is_true (x < y).

Global Instance pre_term_lexico_irrefl :
  Irreflexive (@lexico PreTerm.pre_term _).
Proof. move=> x Hx; move: Hx; by rewrite /lexico /pre_term_lexico ltxx. Qed.

Global Instance pre_term_lexico_trans :
  Transitive (@lexico PreTerm.pre_term _).
Proof. move=> x y z; exact: lt_trans. Qed.

Global Instance pre_term_lexico_strict :
  StrictOrder (@lexico PreTerm.pre_term _).
Proof. split; apply _. Qed.

Global Instance pre_term_lexico_trichotomyT :
  TrichotomyT (@lexico PreTerm.pre_term _).
Proof.
refine (fun x y =>
  match Sumbool.sumbool_of_bool (x < y) with
  | left p => inleft (left p)
  | right p =>
      match Sumbool.sumbool_of_bool (y < x) with
      | left q => inright q
      | right q => inleft (right _)
      end
  end).
abstract (by apply/eqP; rewrite eq_le !leNgt p q).
Defined.

(** [pt_order] is the reflexive closure of [lexico]: this is what lets a single
    HeapLang comparison closure serve both [twp_insertion_sort pt_order] (which
    wants [bool_decide (pt_order x y)]) and [twp_leq_list] (which wants
    [bool_decide (x = y ∨ lexico x y)]). *)
Lemma pt_order_lexico x y : pt_order x y ↔ x = y ∨ lexico x y.
Proof.
rewrite /pt_order /lexico /pre_term_lexico le_eqVlt.
split.
- case/orP => H; [left; by apply/eqP | by right].
- case=> [->|H]; apply/orP; [left; by apply/eqP | by right].
Qed.

Lemma bool_decide_pt_order x y :
  bool_decide (pt_order x y) = (x <= y).
Proof.
case: (bool_decide_reflect (pt_order x y)) => H.
- by move: H; rewrite /pt_order => ->.
- by move: H; rewrite /pt_order => /negP/negbTE ->.
Qed.

(** The derived order on products is stdpp's [lexico] on the factor lists. *)
Lemma pt_order_mul (ts1 ts2 : list PreTerm.pre_term) :
  pt_order (PreTerm.PTMul ts1) (PreTerm.PTMul ts2) ↔ ts1 = ts2 ∨ lexico ts1 ts2.
Proof.
rewrite /pt_order PreTerm.leqE /=.
elim: ts1 ts2 => [|t1 ts1 IH] [|t2 ts2].
- split=> _; by [left|].
- split=> _; by [right|].
- split; first done.
  by case=> [//|].
have el : lexico (t1 :: ts1) (t2 :: ts2)
          ↔ lexico t1 t2 ∨ (t1 = t2 ∧ lexico ts1 ts2) by [].
rewrite lexi_cons el /lexico /pre_term_lexico.
case: (ltgtP t1 t2) => [lt12|lt21|<-].
- split=> _; by [right; left|].
- split => //= H; exfalso; move: lt21; suff -> : t1 = t2 by rewrite ltxx.
  by case: H => [[//]|[//|[]//]].
- rewrite /= IH; split.
  + by case=> [->|H]; [left | right; right].
  + by case=> [[->]|[//|[_ H]]]; [left | right].
Qed.

End PreTermLexico.

(** ** Pure, stdpp-side comparison functions

    [primitives/pre_term.v] implements the derived order in HeapLang, and its
    specs must not mention mathcomp.  We therefore give each layer of the
    comparison a pure Rocq counterpart defined without mathcomp, and prove here
    (where mathcomp is available) that it agrees with the derived order.  The
    HeapLang specs downstream are then stated against these functions. *)

Definition int_of_term_op2 (o : term_op2) : Z :=
  match o with
  | O2Pair => TPair_tag
  | O2Seal => TSeal_tag
  | O2Exp => TExp_tag
  end.

Definition kt_le (k1 k2 : key_type) : bool :=
  bool_decide (int_of_key_type k1 <= int_of_key_type k2)%Z.

Definition op0_le (o1 o2 : term_op0) : bool :=
  match o1, o2 with
  | O0Int n1, O0Int n2 => bool_decide (n1 <= n2)%Z
  | O0Nonce a1, O0Nonce a2 => bool_decide (nonce_loc a1 ≤ₗ nonce_loc a2)
  | O0Int _, O0Nonce _ => true
  | O0Nonce _, O0Int _ => false
  end.

Definition op1_le (o1 o2 : term_op1) : bool :=
  match o1, o2 with
  | O1Key k1, O1Key k2 => kt_le k1 k2
  | O1Key _, _ => true
  | O1Hash, O1Key _ => false
  | O1Hash, _ => true
  | O1Inv, O1Inv => true
  | O1Inv, _ => false
  end.

Definition op2_le (o1 o2 : term_op2) : bool :=
  bool_decide (int_of_term_op2 o1 <= int_of_term_op2 o2)%Z.

Section OrderE.
#[warnings="-ambiguous-paths"]
Import Order.POrderTheory Order.TotalTheory ssrbool boot.eqtype.
Open Scope order_scope.

Lemma kt_leE k1 k2 : kt_le k1 k2 = (k1 <= k2).
Proof. by case: k1; case: k2. Qed.

Lemma op0_leE o1 o2 : op0_le o1 o2 = (o1 <= o2).
Proof.
rewrite PreTerm.op0_leqE; case: o1 o2 => [n1|[l1]] [n2|[l2]] //=.
- by apply/(sameP (bool_decide_reflect _))/(iffP (Z.leb_spec0 _ _)).
- by apply/(sameP (bool_decide_reflect _))/(iffP (Z.leb_spec0 _ _)).
Qed.

Lemma op1_leE o1 o2 : op1_le o1 o2 = (o1 <= o2).
Proof. by rewrite PreTerm.op1_leqE; case: o1 o2 => [k1||] [k2||] //=; rewrite kt_leE. Qed.

Lemma op2_leE o1 o2 : op2_le o1 o2 = (o1 <= o2).
Proof. by case: o1; case: o2. Qed.

(** The stdpp-side structural equation for the derived order on pre-terms: the
    exact shape the HeapLang [leq_term] branches on.  This is [base.leqE] with
    every mathcomp notion replaced by its stdpp counterpart — [==] by
    [bool_decide], [<=%O] on the operator types by [op0_le]/[op1_le]/[op2_le],
    [<=%O] on pre-terms by [bool_decide (pt_order _ _)], and the [seqlexi] order
    on the factor lists by stdpp's [lexico] (see [pt_order_mul]). *)
Lemma pt_orderE pt1 pt2 :
  bool_decide (pt_order pt1 pt2) =
  if bool_decide (PreTerm.cons_num pt1 = PreTerm.cons_num pt2) then
    match pt1, pt2 with
    | PreTerm.PT0 o1, PreTerm.PT0 o2 => op0_le o1 o2
    | PreTerm.PT1 o1 t1, PreTerm.PT1 o2 t2 =>
        if bool_decide (o1 = o2) then bool_decide (pt_order t1 t2)
        else op1_le o1 o2
    | PreTerm.PT2 o1 t11 t12, PreTerm.PT2 o2 t21 t22 =>
        if bool_decide (o1 = o2) then
          (if bool_decide (t11 = t21) then bool_decide (pt_order t12 t22)
           else bool_decide (pt_order t11 t21))
        else op2_le o1 o2
    | PreTerm.PTMul ts1, PreTerm.PTMul ts2 =>
        bool_decide (ts1 = ts2 ∨ lexico ts1 ts2)
    | _, _ => false
    end
  else bool_decide (PreTerm.cons_num pt1 <= PreTerm.cons_num pt2)%Z.
Proof.
rewrite bool_decide_pt_order PreTerm.leqE.
rewrite (_ : bool_decide (PreTerm.cons_num pt1 = PreTerm.cons_num pt2)
             = (PreTerm.cons_num pt1 == PreTerm.cons_num pt2)); last first.
  by apply/(sameP (bool_decide_reflect _))/eqP.
case: (PreTerm.cons_num pt1 == PreTerm.cons_num pt2); last first.
  by apply/(sameP (Z.leb_spec0 _ _))/bool_decide_reflect.
case: pt1 pt2 => [o1|o1 t1|o1 t11 t12|ts1] [o2|o2 t2|o2 t21 t22|ts2] //=.
- by rewrite op0_leE.
- by rewrite op1_leE bool_decide_pt_order eq_op_bool_decide.
- by rewrite op2_leE !bool_decide_pt_order !eq_op_bool_decide.
- by rewrite -(bool_decide_ext _ _ (pt_order_mul ts1 ts2))
             bool_decide_pt_order PreTerm.leqE /=.
Qed.

End OrderE.

(* Bridge between mathcomp's [sort <=%O] and stdpp's [merge_sort pt_order]: both
   are *the* sorted permutation of the input under the (antisymmetric, total)
   order, so they coincide.  Lives here because resolving [merge_sort]'s
   decidability instance needs stdpp's [sorting] typeclass machinery, which the
   (mathcomp-only) [term] layer downstream cannot import. *)
Section SortMergeSort.
Import Order.POrderTheory Order.TotalTheory ssrbool.
Open Scope order_scope.

Lemma sorted_StronglySorted (l : list PreTerm.pre_term) :
  is_true (path.sorted <=%O l) -> StronglySorted pt_order l.
Proof.
elim: l => [_|x l IH]; first by constructor.
move=> Hs.
have Hl : is_true (path.sorted <=%O l) := path.path_sorted Hs.
have Ha : is_true (seq.all (<=%O x) l) := path.order_path_min le_trans Hs.
constructor; first exact: IH Hl.
by elim: l Ha {IH Hl Hs} => [//|y l IH] /ssrbool.andP [xy /IH ?]; constructor.
Qed.

Lemma sort_merge_sort (l : list PreTerm.pre_term) :
  path.sort <=%O l = merge_sort pt_order l.
Proof.
have Hss : StronglySorted pt_order (path.sort <=%O l).
  apply: sorted_StronglySorted; exact: (path.sort_sorted le_total).
rewrite -{1}(merge_sort_id _ _ Hss).
apply: merge_sort_Permutation_eq.
apply/perm_Perm; rewrite path.perm_sort; exact: seq.perm_refl.
Qed.

End SortMergeSort.

Global Instance repr_term_op0_inj : Inj (=) (=) (@repr term_op0 _).
Proof. by case=> [?|[?]] [?|[?]] //= [<-]. Qed.

Global Instance repr_term_op1_inj : Inj (=) (=) (@repr term_op1 _).
Proof. by case=> [?||] [?||] //= [/int_of_key_type_inj ->]. Qed.

Global Instance repr_term_op2_inj : Inj (=) (=) (@repr term_op2 _).
Proof. by case=> [] []. Qed.

Global Instance val_of_pre_term_inj : Inj (=) (=) val_of_pre_term.
Proof.
elim.
- by move=> o1 [] //= o2 [] /repr_term_op0_inj ->.
- by move=> o1 t1 IH [] //= o2 t2 [] /repr_term_op1_inj -> /IH ->.
- move=> o1 t11 IH1 t12 IH2 [] //= o2 t21 t22.
  by move=> [] /repr_term_op2_inj -> /IH1 -> /IH2 ->.
move=> ts1 IHts [] //= ts2 [] e_ts; congr PreTerm.PTMul.
move: e_ts; rewrite repr_list_unseal.
elim: ts1 IHts ts2 => /= [_ [] //|t1 ts1 H [] IHt {}/H IHts].
by case=> //= t2 ts2 [] /IHt -> /IHts ->.
Qed.
