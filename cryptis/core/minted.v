From elpi.apps Require Import locker.
From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap list reservation_map excl.
From iris.algebra Require Import functions.
From iris.base_logic.lib Require Import saved_prop invariants.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib.
From cryptis.core Require Import term.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Minted.

Context `{heapGS Σ}.

Notation iProp := (iProp Σ).

lock Definition minted t : iProp :=
  [∗ set] a ∈ nonces_of_term t, meta (nonce_loc a) (nroot.@"minted") ().

Global Instance Persistent_minted t : Persistent (minted t).
Proof. rewrite unlock; apply _. Qed.

Global Instance Timeless_minted t : Timeless (minted t).
Proof. rewrite unlock; apply _. Qed.

Lemma subterm_minted t1 t2 :
  subterm t1 t2 → minted t2 -∗ minted t1.
Proof.
rewrite unlock !big_sepS_forall; iIntros "%sub m_t2 %t %t_t1".
move/subterm_nonces_of_term in sub.
iApply "m_t2". iPureIntro. set_solver.
Qed.

Lemma minted_TInt n : minted (TInt n) ⊣⊢ True.
Proof. by rewrite unlock nonces_of_termE big_sepS_empty. Qed.

Lemma minted_TPair t1 t2 : minted (TPair t1 t2) ⊣⊢ minted t1 ∧ minted t2.
Proof. by rewrite unlock nonces_of_termE !big_sepS_union_pers. Qed.

Lemma minted_TNonce a : minted (TNonce a) ⊣⊢ meta (nonce_loc a) (nroot.@"minted") ().
Proof. by rewrite unlock nonces_of_termE big_sepS_singleton. Qed.

Lemma minted_TKey kt t : minted (TKey kt t) ⊣⊢ minted t.
Proof. by rewrite unlock nonces_of_termE. Qed.

Lemma minted_TSeal k t : minted (TSeal k t) ⊣⊢ minted k ∧ minted t.
Proof. by rewrite unlock nonces_of_termE !big_sepS_union_pers. Qed.

Lemma minted_THash t : minted (THash t) ⊣⊢ minted t.
Proof. by rewrite unlock nonces_of_termE. Qed.

Lemma minted_TInv t : minted (TInv t) ⊣⊢ minted t.
Proof. by rewrite unlock nonces_of_termE. Qed.

Lemma minted_TExpN t ts :
  ~ is_exp t -> is_true (atomic ts) -> invs_canceled ts ->
  minted (TExpN t ts) ⊣⊢ minted t ∧ [∗ list] t' ∈ ts, minted t'.
Proof.
move => /negb_True nx atom ic.
rewrite unlock (nonces_of_term_TExpN (proj2 (is_trueP _) nx) atom).
rewrite (cancel_invs_canceled atom ic) big_sepS_union_pers.
by rewrite big_sepS_union_list_pers big_sepL_fmap.
Qed.

Lemma minted_TMulN ts :
  is_true (wf_mul_list ts) ->
  minted (TMulN ts) ⊣⊢ [∗ list] t ∈ ts, minted t.
Proof.
move => wf.
rewrite unlock (nonces_of_term_TMulN (proj1 (is_trueP _) wf)).
by rewrite big_sepS_union_list_pers big_sepL_fmap.
Qed.

Lemma minted_base_exps t :
  minted t ⊣⊢ minted (base t) ∧ [∗ list] t' ∈ exps t, minted t'.
Proof.
rewrite -{1}[t]base_expsK minted_TExpN //; last exact: invs_canceled_exps.
exact: atom_exps.
Qed.

Lemma all_minted_TExpN t ts :
  minted t ∧ ([∗ list] t' ∈ ts, minted t') ⊢ minted (TExpN t ts).
Proof.
rewrite unlock !big_sepS_forall.
iIntros "[Ht Hts]" (l) "%l_in".
have /elem_of_subseteq in_nonces := nonces_of_term_TExpN_subseteq t ts.

move: l_in => /(in_nonces l). rewrite elem_of_union elem_of_union_list.
case => [?|]; first by iApply "Ht".
case => _ [] /list_elem_of_fmap [] t' [] -> ??.
rewrite big_sepL_elem_of // big_sepS_forall.
by iApply "Hts".
Qed.

(* Elimination form of [minted] over a product's factors — holds for all [t]
   ([tfactors] of a non-product is the singleton, of a product its canonical
   factors), so no [wf_mul_list] side condition is needed. *)
Lemma minted_tfactors t :
  minted t ⊣⊢ [∗ list] t' ∈ tfactors t, minted t'.
Proof.
rewrite unlock (nonces_of_term_tfactors t).
by rewrite big_sepS_union_list_pers big_sepL_fmap.
Qed.

(* [minted] distributes over exponentiation for *all* exponents [t2] — a product
   exponent flattens into the factor list without changing the nonces, so the
   [~~ is_mul t2] guard is unnecessary.  ([~ is_exp t1] is still needed: for an
   exponential base the new exponent can cancel with the base's own exponent.) *)
Lemma minted_TExp t1 t2 :
  ~ is_exp t1 -> minted (TExp t1 t2) ⊣⊢ minted t1 ∧ minted t2.
Proof.
move => nx.
have -> : TExp t1 t2 = TExpN t1 (tfactors t2) by rewrite /TExpN tfactorsK.
rewrite (minted_TExpN nx (atom_tfactors t2)
           (proj1 (is_trueP _) (invs_canceled_tfactors t2))).
by rewrite -minted_tfactors.
Qed.

Lemma all_minted_TExp t1 t2 :
  minted t1 ∧ minted t2 ⊢ minted (TExp t1 t2).
Proof.
have -> : TExp t1 t2 = TExpN t1 (tfactors t2) by rewrite /TExpN tfactorsK.
rewrite (minted_tfactors t2).
exact: (all_minted_TExpN t1 (tfactors t2)).
Qed.

Lemma minted_nonces_of_term t :
  minted t ⊣⊢ [∗ set] a ∈ nonces_of_term t, minted (TNonce a).
Proof.
rewrite {1}unlock. apply: big_sepS_proper => a a_t.
by rewrite minted_TNonce.
Qed.

Lemma minted_to_list t ts :
  Spec.to_list t = Some ts →
  minted t -∗ [∗ list] t' ∈ ts, minted t'.
Proof.
elim/term_ind': t ts => //=.
  by case=> // ts [<-] /=; iIntros "?".
move=> t _ tl IH ts.
case e: (Spec.to_list tl) => [ts'|] // [<-] /=.
rewrite minted_TPair /=; iIntros "[??]"; iFrame.
by iApply IH.
Qed.

Lemma minted_of_list ts :
  minted (Spec.of_list ts) ⊣⊢
  [∗ list] t ∈ ts, minted t.
Proof.
rewrite Spec.of_list_unseal.
elim: ts => [|t ts IH]; first by rewrite minted_TInt.
by rewrite minted_TPair /= IH bi.persistent_and_sep.
Qed.

Lemma minted_Tag N : ⊢ minted (Tag N).
Proof. by rewrite Tag_unseal minted_TInt. Qed.

Lemma minted_tag N t : minted (Spec.tag (Tag N) t) ⊣⊢ minted t.
Proof.
rewrite Spec.tag_unseal minted_TPair; iSplit.
- by iIntros "[_ ?]".
- iIntros "?"; iSplit => //. iApply minted_Tag.
Qed.

Lemma minted_pkey k : minted (Spec.pkey k) ⊣⊢ minted k.
Proof.
by case: k => // - [] //= ?; rewrite !minted_TKey.
Qed.

Lemma minted_aenc k : minted (AEncKey k) ⊣⊢ minted k.
Proof. by rewrite [term_of_aenc_key]unlock minted_TKey. Qed.

Lemma minted_senc k : minted (SEncKey k) ⊣⊢ minted k.
Proof. by rewrite [term_of_senc_key]unlock minted_TKey. Qed.

Lemma minted_sign k : minted (SignKey k) ⊣⊢ minted k.
Proof. by rewrite [term_of_sign_key]unlock minted_TKey. Qed.

End Minted.
