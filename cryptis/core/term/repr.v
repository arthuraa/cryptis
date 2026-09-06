From cryptis Require Import lib.
From elpi.apps Require Import locker.
From mathcomp Require Import ssreflect.
From Stdlib Require Import ZArith.ZArith Lia.
From stdpp Require Import sorting gmap.
From cryptis.lib Require Import list_sort mathcomp_compat sms.
From iris.heap_lang Require locations.
From iris.heap_lang Require Import notation.
From iris.heap_lang Require Import primitive_laws.
From cryptis.core Require Export pre_term.
From cryptis.core.term Require Import base algebra tsize.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Implicit Types (t k : term) (ts : list term).

(* The HeapLang value embedding (val_of_term / repr), the Infinite instance, and term_height. *)

Section ValOfTerm.

Fixpoint val_of_term_rec t : val :=
  match t with
  | TInt n =>
    (#TOp0_tag, (#TInt_tag, #n))
  | TPair t1 t2 =>
    (#TOp2_tag, (#TPair_tag, val_of_term_rec t1, val_of_term_rec t2))%V
  | TNonce l =>
    (#TOp0_tag, (#TNonce_tag, #(nonce_loc l)))%V
  | TKey kt t =>
    (#TOp1_tag, ((#TKey_tag, repr kt), val_of_term_rec t))%V
  | TSeal t1 t2 =>
    (#TOp2_tag, (#TSeal_tag, val_of_term_rec t1, val_of_term_rec t2))%V
  | THash t =>
    (#TOp1_tag, ((#THash_tag, #()), val_of_term_rec t))%V
  | TNonFree pt _ _ => val_of_pre_term pt
  end.

Definition val_of_term_aux : seal val_of_term_rec. by eexists. Qed.
Definition val_of_term : term -> val := unseal val_of_term_aux.
Lemma val_of_term_unseal : val_of_term = val_of_term_rec.
Proof. exact: seal_eq. Qed.
Coercion val_of_term : term >-> val.
Global Instance repr_term : Repr term := val_of_term.

Global Instance repr_aenc_key : Repr aenc_key := λ k : aenc_key, val_of_term (term_of_aenc_key k).
Global Instance repr_senc_key : Repr senc_key := λ k : senc_key, val_of_term (term_of_senc_key k).
Global Instance repr_sign_key : Repr sign_key := λ k : sign_key, val_of_term (term_of_sign_key k).

Lemma val_of_pre_term_unfold t :
  val_of_pre_term (unfold_term t) = val_of_term t.
Proof.
rewrite val_of_term_unseal.
elim/term_ind': t => //=; try by move=> *; congruence.
Qed.

End ValOfTerm.

Arguments repr_term /.

Global Instance val_of_term_inj : Inj (=) (=) val_of_term.
Proof.
move=> t1 t2 e_t1t2; apply: unfold_term_inj.
apply: val_of_pre_term_inj.
by rewrite !val_of_pre_term_unfold.
Qed.

Global Instance infinite_term : Infinite term.
Proof.
pose int_of_term (t : term) :=
  if t is TInt n then Some n else None.
apply (inj_infinite TInt int_of_term).
by move=> n; rewrite /int_of_term.
Qed.

Definition term_height t :=
  PreTerm.height (unfold_term t).

