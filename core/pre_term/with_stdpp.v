From cryptis Require Import mathcomp_compat lib.
From mathcomp Require Import ssreflect.
From mathcomp Require eqtype ssrbool path.
From deriving Require Import deriving.
From stdpp Require Import gmap.
From iris.heap_lang Require Import notation.
From iris.heap_lang Require Import primitive_laws.
From cryptis.core.pre_term Require Import base.

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
Proof.
refine (
  fun kt1 kt2 =>
    match kt1, kt2 with
    | AEnc, AEnc => left _
    | ADec, ADec => left _
    | Sign, Sign => left _
    | Verify, Verify => left _
    | SEnc, SEnc => left _
    | _, _ => right _
    end); congruence.
Defined.

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

Section ValOfPreTerm.

Import PreTerm.

Fixpoint val_of_pre_term_rec pt : val :=
  match pt with
  | PTInt n =>
    (#TInt_tag, #n)
  | PTPair t1 t2 =>
    (#TPair_tag, (val_of_pre_term_rec t1, val_of_pre_term_rec t2))%V
  | PTNonce l =>
    (#TNonce_tag, #l)%V
  | PTKey kt t =>
    (#TKey_tag, (#(int_of_key_type kt), val_of_pre_term_rec t))%V
  | PTSeal t1 t2 =>
    (#TSeal_tag, (val_of_pre_term_rec t1, val_of_pre_term_rec t2))%V
  | PTHash t =>
    (#THash_tag, val_of_pre_term_rec t)
  | PTExp t ts =>
    (#TExp_tag, (val_of_pre_term_rec t,
                 repr_list (map val_of_pre_term_rec ts)))
  end.

Definition val_of_pre_term_aux : seal val_of_pre_term_rec. by eexists. Qed.
Definition val_of_pre_term : Repr pre_term := unseal val_of_pre_term_aux.
Lemma val_of_pre_term_unseal : val_of_pre_term = val_of_pre_term_rec.
Proof. exact: seal_eq. Qed.
Global Existing Instance val_of_pre_term.

End ValOfPreTerm.

Fixpoint nonces_of_pre_term pt : gset loc :=
  match pt with
  | PreTerm.PTInt _ => ∅
  | PreTerm.PTPair t1 t2 => nonces_of_pre_term t1 ∪ nonces_of_pre_term t2
  | PreTerm.PTNonce l => {[l]}
  | PreTerm.PTKey _ t => nonces_of_pre_term t
  | PreTerm.PTSeal t1 t2 => nonces_of_pre_term t1 ∪ nonces_of_pre_term t2
  | PreTerm.PTHash t => nonces_of_pre_term t
  | PreTerm.PTExp t ts => nonces_of_pre_term t ∪ ⋃ map nonces_of_pre_term ts
  end.

Global Instance pre_term_inhabited : Inhabited PreTerm.pre_term.
Proof. exact: (populate (PreTerm.PTInt 0)). Qed.

Definition pre_term_eq_dec : EqDecision PreTerm.pre_term :=
  Eval hnf in def_eq_decision _.
Global Existing Instance pre_term_eq_dec.
