From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import reservation_map.
From iris.heap_lang Require Import notation proofmode adequacy.
From iris.heap_lang.lib Require Import par ticket_lock assert.
From cryptis Require Import lib role cryptis primitives tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Existing Instance ticket_lock.

Section TermSet.

Context `{!heapGS Σ, !spawnG Σ, !cryptisGS Σ, !tlockG Σ}.
Notation iProp := (iProp Σ).

Implicit Types (rl : role) (t kI kR nI nR sI sR kS : term).

Definition is_term_set N v (xs : list term) : iProp := ∃ (lset : loc),
  ⌜v = #lset⌝ ∗
  lset ↦ (repr xs) ∗
  [∗ list] x ∈ xs, term_meta x N ().

Definition new_term_set : val := λ: <>, ref []%V.

Lemma wp_new_term_set N :
  {{{ True }}}
    new_term_set #()
  {{{v, RET v; is_term_set N v [] }}}.
Proof.
iIntros "%Φ _ post".
wp_lam. wp_apply (@wp_nil term).
wp_alloc set as "set".
iApply "post". iModIntro. iExists set.
iFrame. by eauto.
Qed.

Definition add_term_set : val := λ: "x" "set",
  "set" <- "x" :: !"set".

Lemma wp_add_term_set N v x xs :
  {{{ term_token x (↑N) ∗ is_term_set N v xs }}}
    add_term_set x v
  {{{ RET #(); is_term_set N v (x :: xs) }}}.
Proof.
iIntros "%Φ [token (%l & -> & l & #meta)] post".
iMod (term_meta_set N () with "token") as "#?" => //.
wp_lam. wp_load. wp_cons. wp_store.
iApply "post". iExists l. iFrame. rewrite /=. by eauto.
Qed.

Definition mem_term_set : val := λ: "x" "set",
  match: find_list (λ: "y", eq_term "x" "y") (!"set") with
    SOME <> => #true
  | NONE => #false
  end.

Lemma wp_mem_term_set N (x : term) (xs : list term) v :
  {{{ is_term_set N v xs }}}
    mem_term_set x v
  {{{ RET #(bool_decide (x ∈ xs)); is_term_set N v xs }}}.
Proof.
iIntros "%Φ (%l & -> & l & #meta) post".
wp_lam. wp_pures. wp_load. wp_pures.
wp_apply (wp_find_list (λ y, bool_decide (x = y))) => //.
{ iIntros "%y %Ψ _ post". wp_pures.
  iApply wp_eq_term. by iApply "post". }
iIntros "_".
assert (find (λ y, bool_decide (x = y)) xs =
          if bool_decide (x ∈ xs) then Some x else None) as ->.
{ elim: xs => //= y xs ->.
  case: (bool_decide_reflect (x = y)) => [->|xy].
  - by rewrite bool_decide_eq_true_2 // elem_of_cons; eauto.
  - rewrite (bool_decide_ext (x ∈ xs) (x ∈ y :: xs)) //.
    rewrite elem_of_cons; intuition congruence. }
iAssert (is_term_set N #l xs) with "[l]" as "set".
{ iExists l. iFrame. by eauto. }
iSpecialize ("post" with "set").
by case: bool_decide; wp_pures; iApply "post".
Qed.

Lemma is_term_set_fresh N v x xs :
  is_term_set N v xs -∗
  term_token x (↑N) -∗
  ⌜x ∉ xs⌝.
Proof.
iIntros "(%l & -> & l & #meta) token %x_xs".
rewrite big_sepL_elem_of //.
by iDestruct (term_meta_token with "token meta") as "[]".
Qed.

Definition is_lock_term_set N v : iProp := ∃ vset vlock γ,
  ⌜v = (vset, vlock)%V⌝ ∗
  is_lock γ vlock (∃ xs, is_term_set N vset xs).

Instance is_lock_term_set_persistent N v :
  Persistent (is_lock_term_set N v).
Proof. apply _. Qed.

Definition new_lock_term_set : val := λ: <>,
  let: "set"  := new_term_set #() in
  let: "lock" := newlock #() in
  ("set", "lock").

Lemma wp_new_lock_term_set N :
  {{{ True }}}
    new_lock_term_set #()
  {{{ v, RET v; is_lock_term_set N v }}}.
Proof.
iIntros "%Φ _ post".
wp_lam. wp_apply (wp_new_term_set N) => //.
iIntros "%vset set". wp_pures.
wp_apply (newlock_spec (∃ xs, is_term_set N vset xs) with "[set]");
  first by eauto.
iIntros "%vlock %γ #lock". wp_pures.
iApply "post". iModIntro. iExists vset, vlock, γ. eauto.
Qed.

Definition add_fresh_lock_term_set : val := λ: "x" "set",
  acquire (Snd "set");;
  let: "xs" := Fst "set" in
  assert: (~ mem_term_set "x" "xs");;
  add_term_set "x" "xs";;
  release (Snd "set").

Lemma wp_add_fresh_lock_term_set N x v :
  {{{ is_lock_term_set N v ∗ term_token x (↑N) }}}
    add_fresh_lock_term_set x v
  {{{ RET #(); True }}}.
Proof.
iIntros "%Φ [(%vset & %vlock & %γ & -> & #lock) token] post".
wp_lam. wp_pures. wp_apply acquire_spec => //.
iIntros "[locked (%xs & set)]". wp_pures.
wp_apply wp_assert. wp_apply (wp_mem_term_set with "set"). iIntros "set".
wp_pures.
iPoseProof (is_term_set_fresh with "set token") as "%fresh".
rewrite bool_decide_eq_false_2 => //.
iModIntro. iSplit => //. iIntros "!>".
wp_pures.
wp_apply (wp_add_term_set with "[$]"). iIntros "set". wp_pures.
wp_apply (release_spec with "[locked set] post").
iSplit => //. by iFrame.
Qed.

End TermSet.
