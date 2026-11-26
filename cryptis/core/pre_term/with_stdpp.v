From cryptis Require Import mathcomp_compat lib.
From cryptis.lib Require Import list_sort.
From mathcomp Require Import ssreflect.
From mathcomp Require Import order.
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
  end.

Canonical term_op2O := leibnizO term_op2.

#[global]
Instance term_op2_eq_dec : EqDecision term_op2.
Proof. exact: def_eq_decision. Defined.

Instance repr_term_op2 : Repr term_op2 := λ o,
  match o with
  | O2Pair => #TPair_tag
  | O2Seal => #TSeal_tag
  end.

Section ValOfPreTerm.

Import PreTerm.

(** The encodings of monomials, polynomials and fractions take the encoding
    of the atoms as a parameter: they coincide with the [repr] of
    [Poly.poly] and [Frac.frac], so that [primitives/poly.v] runs on them. *)
Definition val_mono (v : pre_term → val) (m : list pre_term) : val :=
  repr_list (map v m).

Definition val_poly (v : pre_term → val) (A : poly_lists) : val :=
  (repr_list (map (val_mono v) A.1), repr_list (map (val_mono v) A.2))%V.

Definition val_frac (v : pre_term → val) (F : frac_lists) : val :=
  (val_poly v F.1, val_poly v F.2)%V.

Definition val_of_pre_term : Repr pre_term := fix val_of_pre_term pt :=
  match pt with
  | PT0 o =>
    (#TOp0_tag, repr o)%V
  | PT1 o t =>
    (#TOp1_tag, (repr o, val_of_pre_term t))%V
  | PT2 o t1 t2 =>
    (#TOp2_tag, (repr o, val_of_pre_term t1, val_of_pre_term t2))%V
  | PTMod f =>
    (#TMod_tag, val_frac val_of_pre_term f)%V
  | PTDH l =>
    (#TDH_tag,
     repr_list (map (λ e, (val_of_pre_term e.1,
                           val_frac val_of_pre_term e.2)%V) l))%V
  end.

#[global] Existing Instance val_of_pre_term.

End ValOfPreTerm.

Definition nonce_eq_dec : EqDecision nonce := Eval hnf in def_eq_decision _.
#[global] Existing Instance nonce_eq_dec.
#[global] Instance nonce_countable : Countable nonce.
Proof. exact: def_countable. Qed.
#[global] Instance nonce_inhabited : Inhabited nonce :=
  populate (Nonce inhabitant).

Definition nonces_of_term_op0 o : gset nonce :=
  match o with
  | O0Int _ => ∅
  | O0Nonce a => {[a]}
  end.

Definition nonces_of_frac (n : PreTerm.pre_term → gset nonce)
    (F : PreTerm.frac_lists) : gset nonce :=
  let nonces_monos ms := ⋃ map (λ m, ⋃ map n m) ms in
  nonces_monos F.1.1 ∪ nonces_monos F.1.2 ∪
  nonces_monos F.2.1 ∪ nonces_monos F.2.2.

Fixpoint nonces_of_pre_term pt : gset nonce :=
  match pt with
  | PreTerm.PT0 o => nonces_of_term_op0 o
  | PreTerm.PT1 _ t => nonces_of_pre_term t
  | PreTerm.PT2 _ t1 t2 => nonces_of_pre_term t1 ∪ nonces_of_pre_term t2
  | PreTerm.PTMod f => nonces_of_frac nonces_of_pre_term f
  | PreTerm.PTDH l =>
    ⋃ map (λ e, nonces_of_pre_term e.1 ∪
                nonces_of_frac nonces_of_pre_term e.2) l
  end.

#[global] Instance pre_term_inhabited : Inhabited PreTerm.pre_term.
Proof. exact: (populate (PreTerm.PT0 (O0Int 0))). Qed.

Definition pre_term_eq_dec : EqDecision PreTerm.pre_term :=
  Eval hnf in def_eq_decision _.
#[global] Existing Instance pre_term_eq_dec.

#[global] Instance pre_term_countable : Countable PreTerm.pre_term :=
  def_countable _ pre_term_eq_dec.

(** ** Order

    [lexico] is the strict part of the order derived in [base.v], and
    [pt_order] is the order itself. *)
Section PreTermOrder.
#[warnings="-ambiguous-paths"]
Import Order.POrderTheory Order.TotalTheory ssrbool boot.eqtype.
Open Scope order_scope.

(* [is_true] is spelled out so that the relations land on ssreflect's boolean
   coercion, which the mathcomp order lemmas expect, rather than stdpp's
   [Is_true]. *)
#[global] Instance pre_term_lexico : Lexico PreTerm.pre_term :=
  λ x y, is_true (x < y).

#[global] Instance pre_term_lexico_strict :
  StrictOrder (@lexico PreTerm.pre_term _).
Proof.
split; first by move=> x; rewrite /complement /lexico /pre_term_lexico ltxx.
move=> x y z; exact: lt_trans.
Qed.

#[global] Instance pre_term_lexico_trichotomyT :
  TrichotomyT (@lexico PreTerm.pre_term _).
Proof.
refine (λ x y,
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

Definition pt_order : relation PreTerm.pre_term := λ x y, is_true (x <= y).

#[global] Instance pt_order_dec : RelDecision pt_order :=
  λ x y, bool_eq_dec (x <= y) true.

Lemma pt_order_lexico x y : pt_order x y ↔ x = y ∨ lexico x y.
Proof.
rewrite /pt_order /lexico /pre_term_lexico le_eqVlt.
split; first by case/orP => H; [left; apply/eqP|right].
by case=> [->|H]; apply/orP; [left|right].
Qed.

Lemma bool_decide_pt_order x y : bool_decide (pt_order x y) = (x <= y).
Proof. by apply/bool_decide_reflect/idP. Qed.

Lemma lexico_pt_cmp x y : lexico x y ↔ PreTerm.pt_cmp x y = Lt.
Proof.
rewrite /lexico /pre_term_lexico PreTerm.pt_ltE.
by case: PreTerm.pt_cmp.
Qed.

Lemma bool_decide_pt_order_cmp x y :
  bool_decide (pt_order x y) = PreTerm.pt_le x y.
Proof. by rewrite bool_decide_pt_order PreTerm.pt_leE. Qed.

End PreTermOrder.

Definition int_of_term_op2 (o : term_op2) : Z :=
  match o with O2Pair => TPair_tag | O2Seal => TSeal_tag end.

(** The comparisons of the operators, as the HeapLang comparison of their
    encodings computes them. *)
Section OpCmp.
#[warnings="-ambiguous-paths"]
Import Order.POrderTheory Order.TotalTheory ssrbool boot.eqtype.
Open Scope order_scope.

Lemma cmp_ord_Z (n1 n2 : Z) : PreTerm.cmp_ord n1 n2 = Z.compare n1 n2.
Proof.
rewrite /PreTerm.cmp_ord; case: (Z.compare_spec n1 n2) => [->|lt|gt].
- by rewrite eqxx.
- have -> : (n1 == n2) = false by apply/eqP; lia.
  by have -> : (n1 <= n2)%O = true by apply/Z.leb_le; lia.
- have -> : (n1 == n2) = false by apply/eqP; lia.
  by have -> : (n1 <= n2)%O = false by apply/Z.leb_nle; lia.
Qed.

#[local] Lemma le_alt d (T : orderType d) (x y : T) :
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

Lemma op0_eqE (o1 o2 : term_op0) :
  (o1 == o2) =
  match o1, o2 with
  | O0Int n1, O0Int n2 => n1 == n2
  | O0Nonce a1, O0Nonce a2 => a1 == a2
  | _, _ => false
  end.
Proof.
by case: o1 o2 => [n1|a1] [n2|a2] //=; apply/eqP/eqP => [[]|->].
Qed.

Lemma cmp_op0E (o1 o2 : term_op0) :
  PreTerm.cmp_ord o1 o2 =
  match o1, o2 with
  | O0Int n1, O0Int n2 => Z.compare n1 n2
  | O0Nonce a1, O0Nonce a2 =>
    Z.compare (locations.loc_car (nonce_loc a1))
              (locations.loc_car (nonce_loc a2))
  | O0Int _, O0Nonce _ => Lt
  | O0Nonce _, O0Int _ => Gt
  end.
Proof.
rewrite /PreTerm.cmp_ord op0_eqE op0_leqE.
case: o1 o2 => [n1|[l1]] [n2|[l2]] //.
- exact: cmp_ord_Z.
- rewrite -cmp_ord_Z /PreTerm.cmp_ord.
  have -> : (Nonce l1 == Nonce l2) = (loc_car l1 == loc_car l2) by [].
  by have -> : (Nonce l1 <= Nonce l2)%O = (loc_car l1 <= loc_car l2)%O by [].
Qed.

Lemma op1_leqE (o1 o2 : term_op1) :
  (o1 <= o2)%O =
  match o1, o2 with
  | O1Key k1, O1Key k2 => (k1 <= k2)%O
  | O1Hash, O1Hash => true
  | O1Key _, _ => true
  | _, _ => false
  end.
Proof. case: o1 o2 => [k1|] [k2|] //=; by rewrite [RHS]le_alt. Qed.

Lemma op1_eqE (o1 o2 : term_op1) :
  (o1 == o2) =
  match o1, o2 with
  | O1Key k1, O1Key k2 => k1 == k2
  | O1Hash, O1Hash => true
  | _, _ => false
  end.
Proof. by case: o1 o2 => [k1|] [k2|] //=; apply/eqP/eqP => [[]|->]. Qed.

Lemma cmp_ord_key_type (k1 k2 : key_type) :
  PreTerm.cmp_ord k1 k2 = Z.compare (int_of_key_type k1) (int_of_key_type k2).
Proof. by case: k1; case: k2. Qed.

Lemma cmp_op1E (o1 o2 : term_op1) :
  PreTerm.cmp_ord o1 o2 =
  match o1, o2 with
  | O1Key k1, O1Key k2 => Z.compare (int_of_key_type k1) (int_of_key_type k2)
  | O1Hash, O1Hash => Eq
  | O1Key _, O1Hash => Lt
  | O1Hash, O1Key _ => Gt
  end.
Proof.
rewrite /PreTerm.cmp_ord op1_eqE op1_leqE.
by case: o1 o2 => [k1|] [k2|] //; rewrite -cmp_ord_key_type.
Qed.

Lemma cmp_op2E (o1 o2 : term_op2) :
  PreTerm.cmp_ord o1 o2 = Z.compare (int_of_term_op2 o1) (int_of_term_op2 o2).
Proof. by case: o1; case: o2. Qed.

End OpCmp.

#[global] Instance repr_term_op0_inj : Inj (=) (=) (@repr term_op0 _).
Proof. by case=> [?|[?]] [?|[?]] //= [<-]. Qed.

#[global] Instance repr_term_op1_inj : Inj (=) (=) (@repr term_op1 _).
Proof. by case=> [?|] [?|] //= [/int_of_key_type_inj ->]. Qed.

#[global] Instance repr_term_op2_inj : Inj (=) (=) (@repr term_op2 _).
Proof. by case=> [] []. Qed.


Lemma repr_list_map_inj {A} (f : A → val) l1 :
  Forall (λ x, ∀ y, f x = f y → x = y) l1 →
  ∀ l2, repr_list (map f l1) = repr_list (map f l2) → l1 = l2.
Proof.
rewrite [@repr_list]unlock.
by elim=> [|x1 l1' Hx _ IH] [|x2 l2] //= [] /Hx -> /IH ->.
Qed.

Lemma val_frac_inj (v : PreTerm.pre_term → val) F :
  PreTerm.frac_all (λ x, ∀ y, v x = v y → x = y) F →
  ∀ F', val_frac v F = val_frac v F' → F = F'.
Proof.
have M ms : PreTerm.monos_all (λ x, ∀ y, v x = v y → x = y) ms →
    ∀ ms', repr_list (map (val_mono v) ms) =
           repr_list (map (val_mono v) ms') → ms = ms'.
  move=> /PreTerm.monos_all_Forall Hms; apply: repr_list_map_inj.
  apply: (Forall_impl _ _ _ Hms) => m Hm m'; exact: repr_list_map_inj.
case: F => [[ps ns] [qs rs]] [[Hps Hns] [Hqs Hrs]] [[ps' ns'] [qs' rs']].
rewrite /val_frac /val_poly /= => H; injection H.
by move=> /(M rs Hrs) -> /(M qs Hqs) -> /(M ns Hns) -> /(M ps Hps) ->.
Qed.

#[global] Instance val_of_pre_term_inj : Inj (=) (=) val_of_pre_term.
Proof.
move=> t1; elim: t1 => [o1|o1 t1 IH|o1 t11 IH1 t12 IH2|f1 IH|l1 IH].
- by case=> //= o2 [] /repr_term_op0_inj ->.
- by case=> //= o2 t2 [] /repr_term_op1_inj -> /IH ->.
- by case=> //= o2 t21 t22 [] /repr_term_op2_inj -> /IH1 -> /IH2 ->.
- case=> //= f2 E; congr PreTerm.PTMod; apply: (val_frac_inj _ _ IH).
  congruence.
- case=> //= l2 [] /(repr_list_map_inj _ l1) -> //.
  apply: (Forall_impl _ _ _ (PreTerm.entries_all_Forall IH)) => -[b F]
    [Hb [HF]].
  rewrite /= in Hb HF; case=> b' F' /= E.
  have [Eb EF] : val_of_pre_term b = val_of_pre_term b' ∧
                 val_frac val_of_pre_term F = val_frac val_of_pre_term F'.
    by split; congruence.
  by rewrite (Hb _ Eb) (val_frac_inj _ _ HF _ EF).
Qed.
