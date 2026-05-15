From cryptis Require Import mathcomp_compat lib.
From mathcomp Require Import ssreflect.
From mathcomp Require eqtype ssrbool path.
From deriving Require Import deriving.
From stdpp Require Import gmap.
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
  | O0Int n => (#0, #n)%V
  | O0Nonce a => (#1, #a)%V
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
  | O1Key kt => (#0, repr kt)%V
  | O1Hash => (#1, #())%V
  | O1Inv => (#2, #())%V
  end.

Canonical term_op2O := leibnizO term_op2.

#[global]
Instance term_op2_eq_dec : EqDecision term_op2.
Proof. exact: def_eq_decision. Defined.

Instance repr_term_op2 : Repr term_op2 := λ o,
  match o with
  | O2Pair => #0
  | O2Seal => #1
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
  | PTExp t ts =>
    (#TExp_tag, (val_of_pre_term t, repr_list (map val_of_pre_term ts)))%V
  end.

Global Existing Instance val_of_pre_term.

End ValOfPreTerm.

Definition nonces_of_term_op0 o : gset loc :=
  match o with
  | O0Int _ => ∅
  | O0Nonce a => {[a]}
  end.

Fixpoint nonces_of_pre_term pt : gset loc :=
  match pt with
  | PreTerm.PT0 o => nonces_of_term_op0 o
  | PreTerm.PT1 _ t => nonces_of_pre_term t
  | PreTerm.PT2 _ t1 t2 => nonces_of_pre_term t1 ∪ nonces_of_pre_term t2
  | PreTerm.PTExp t ts => nonces_of_pre_term t ∪ ⋃ map nonces_of_pre_term ts
  end.

Global Instance pre_term_inhabited : Inhabited PreTerm.pre_term.
Proof. exact: (populate (PreTerm.PT0 (O0Int 0))). Qed.

Definition pre_term_eq_dec : EqDecision PreTerm.pre_term :=
  Eval hnf in def_eq_decision _.
Global Existing Instance pre_term_eq_dec.

Global Instance repr_term_op0_inj : Inj (=) (=) (@repr term_op0 _).
Proof. by case=> [?|?] [?|?] //= [<-]. Qed.

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
move=> t1 IHt ts1 IHts [] //= t2 ts2 [] /IHt -> e_ts; congr PreTerm.PTExp.
move: e_ts; rewrite repr_list_unseal.
elim: ts1 IHts ts2 {t1 t2 IHt} => /= [_ [] //|t1 ts1 H [] IHt {}/H IHts].
by case=> //= t2 ts2 [] /IHt -> /IHts ->.
Qed.
