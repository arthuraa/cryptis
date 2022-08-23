From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib version term cryptis primitives tactics.
From cryptis Require Import role session pk_auth pk_dh.
From cryptis.store Require Import impl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Defs.

Context `{!cryptisG Σ, !heapGS Σ, !sessionG Σ}.
Notation iProp := (iProp Σ).

Class storeG := StoreG {
  store_inG :> inG Σ (authR (max_prefix_listUR termO));
}.

Context `{!storeG}.

Local Instance STORE : PK := PK_DH (λ _ _ _ _, True)%I.

Implicit Types (cs : cst) (ss : sst).
Implicit Types kI kR kS t : term.
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types v : val.

(* FIXME: infer the invariant φ in a tactic, similarly to how iLöb works *)
Lemma wp_sess_recv E N c sk (f : val) φ Φ Ψ :
  ↑cryptisN ⊆ E →
  channel c -∗
  enc_pred N Φ -∗
  sterm sk -∗
  □ (∀ t,
      φ -∗
      ▷ (pterm (TKey Enc sk) ∗ pterm t ∨
         sterm t ∗ □ Φ sk t ∗ □ (pterm (TKey Dec sk) → pterm t)) -∗
      WP f t @ E {{ v, ⌜v = NONEV⌝ ∗ φ ∨ ∃ v', ⌜v = SOMEV v'⌝ ∗ Ψ v' }}) -∗
  φ -∗ WP sess_recv N c (Spec.mkskey sk) f @ E {{ Ψ }}.
Proof.
iIntros "% #chan_c #ΦP #s_sk #wp_f Hφ"; rewrite /sess_recv; wp_pures.
iRevert "Hφ". iApply wp_do_until; iIntros "!> Hφ". wp_pures.
wp_bind (recv _); iApply wp_recv => //.
iIntros "%t #p_t"; wp_pures.
wp_tsdec_eq t' e; wp_pures; eauto.
rewrite {}e {t} pterm_TEnc.
iApply ("wp_f" with "Hφ"). rewrite pterm_tag.
iDestruct "p_t" as "[[??] | p_t]"; eauto.
iRight. rewrite sterm_TEnc sterm_tag.
iDestruct "p_t" as "[[??] [inv_t' p_t]]".
do 2![iSplit => //].
iPoseProof (wf_enc_elim with "inv_t' ΦP") as "{inv_t'} #inv_t'".
eauto.
Qed.

Variable N : namespace.

Definition store_key rl kI kR kS ok γ : iProp := ∃ kS' ph T,
  ⌜kS = Spec.tag (N.@"key") kS'⌝ ∗
  ⌜ok = in_honest kI kR T⌝ ∗
  pk_dh_session_weak N (λ _ _ _ _, True)%I rl kI kR kS' ph T ∗
  if ok then
    pk_dh_session_meta N (λ _ _ _ _, True)%I Init kI kR kS' N γ ∗
    pk_dh_session_key N (λ _ _ _ _, True)%I kI kR kS' ph T ∗
    □ (∀ kt, pterm (TKey kt kS) -∗ ◇ False)
  else True%I.

#[global]
Instance store_key_persistent rl kI kR kS ok γ :
  Persistent (store_key rl kI kR kS ok γ).
Proof. apply _. Qed.

Definition store_pred kS m : iProp := ∃ (n : nat) t kI kR ok γ,
  ⌜m = Spec.of_list [TInt n; t]⌝ ∗
  pterm t ∗
  version_frag γ n t ∗
  store_key Init kI kR kS ok γ.

Definition ack_store_pred kS m : iProp := ∃ (n : nat),
  ⌜m = TInt n⌝. (* FIXME: Do we need anything else here? *)

Definition load_pred (kS m : term) : iProp := True.

Definition ack_load_pred kS m : iProp := ∃ (n : nat) t,
  ⌜m = Spec.of_list [TInt n; t]⌝ ∗
  ∀ kI kR γ t', store_key Init kI kR kS true γ -∗
  version_frag γ n t' -∗
  ⌜t = t'⌝.

Definition ctx : iProp :=
  enc_pred (N.@"store") store_pred ∗
  enc_pred (N.@"ack_store") ack_store_pred ∗
  enc_pred (N.@"load") load_pred ∗
  enc_pred (N.@"ack_load") ack_load_pred ∗
  pk_dh_ctx N (λ _ _ _ _, True)%I ∗
  key_pred (N.@"key") (λ _ _, False)%I.

End Defs.

Arguments storeG Σ : clear implicits.
