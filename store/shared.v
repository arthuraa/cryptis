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
Implicit Types ok : bool.

(* FIXME: infer the invariant φ in a tactic, similarly to how iLöb works *)
Lemma wp_sess_recv E N c sk (f : val) φ Ψ :
  ↑cryptisN ⊆ E →
  channel c -∗
  sterm sk -∗
  □ (∀ t,
      φ -∗
      pterm (TEnc sk (Spec.tag N t)) -∗
      WP f t @ E {{ v, ⌜v = NONEV⌝ ∗ φ ∨ ∃ v', ⌜v = SOMEV v'⌝ ∗ Ψ v' }}) -∗
  φ -∗ WP sess_recv N c (Spec.mkskey sk) f @ E {{ Ψ }}.
Proof.
iIntros "% #chan_c #s_sk #wp_f Hφ"; rewrite /sess_recv; wp_pures.
iRevert "Hφ". iApply wp_do_until; iIntros "!> Hφ". wp_pures.
wp_bind (recv _); iApply wp_recv => //.
iIntros "%t #p_t"; wp_pures.
wp_tsdec_eq t' e; wp_pures; eauto.
rewrite {}e {t}.
by iApply ("wp_f" with "Hφ").
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

Definition version_pred rl kS m : iProp := ∃ (n : nat) t kI kR ok γ,
  ⌜m = Spec.of_list [TInt n; t]⌝ ∗
  pterm t ∗
  (if ok then version_frag γ n t else True) ∗
  store_key rl kI kR kS ok γ.

Definition store_pred kS m : iProp := version_pred Init kS m.

Definition ack_store_pred kS m : iProp := ∃ (n : nat),
  ⌜m = TInt n⌝. (* FIXME: Do we need anything else here? *)

Definition load_pred (kS m : term) : iProp := True.

Definition ack_load_pred kS m : iProp := version_pred Resp kS m.

Definition ctx : iProp :=
  enc_pred (N.@"store") store_pred ∗
  enc_pred (N.@"ack_store") ack_store_pred ∗
  enc_pred (N.@"load") load_pred ∗
  enc_pred (N.@"ack_load") ack_load_pred ∗
  pk_dh_ctx N (λ _ _ _ _, True)%I ∗
  key_pred (N.@"key") (λ _ _, False)%I.

Lemma store_predE_gen N' rl rl' kI kR kS ok γ n t :
  store_key rl kI kR kS ok γ -∗
  enc_pred N' (version_pred rl') -∗
  pterm (TEnc kS (Spec.tag N' (Spec.of_list [TInt n; t]))) -∗
  ▷ (pterm t ∗
     if ok then version_frag γ n t else True%I).
Proof.
iIntros "#key #? #p_m".
iPoseProof (pterm_TEncE with "p_m [//]") as "{p_m} p_m".
iDestruct "key" as "(%kS' & %ph & %T & %e_key & %e_ok & #sessW & #key)".
rewrite pterm_of_list /=.
iDestruct "p_m" as "[(p_key & _ & p_t' & _) | p_m]".
{ case e: ok; last first.
    by do 2?iSplit => //.
  iDestruct "key" as "(#meta & #key & #contra)".
  iDestruct ("contra" with "p_key") as ">[]". }
iDestruct "p_m" as "(#p_m & s_t' & _)".
iDestruct "p_m" as "(%n'' & %t'' & %kI'' & %kR'' & %ok'' & %γ'' & >%e & p_m)".
case/Spec.of_list_inj: e => /Nat2Z.inj <- <- {n'' t''}.
iDestruct "p_m" as "(p_t' & frag'' & p_m)".
case e: ok; last by eauto.
iDestruct "key" as "(#meta & #key & #s_key)".
iModIntro.
iDestruct "p_m" as "(%kS''' & %ph''' & %T''' & %e_key''' & p_m)".
have {kS''' e_key'''} -> : kS''' = kS'.
  rewrite e_key''' in e_key.
  by have [??] := Spec.tag_inj _ _ _ _ e_key.
iDestruct "p_m" as "(%e_ok''' & sessW''' & sess''')".
iDestruct (session_weak_session_key with "sessW''' key")
  as "(-> & -> & -> & ->)".
rewrite e_ok''' -e_ok e.
iDestruct "sess'''" as "(meta''' & _)".
iPoseProof (term_meta_agree with "meta''' meta") as "->".
iFrame. iSplit => //.
Qed.

Lemma store_predE rl kI kR kS ok γ n t :
  store_key rl kI kR kS ok γ -∗
  ctx -∗
  pterm (TEnc kS (Spec.tag (N.@"store") (Spec.of_list [TInt n; t]))) -∗
  ▷ (pterm t ∗
     if ok then version_frag γ n t else True%I).
Proof.
iIntros "#key #(? & _)".
iApply store_predE_gen; eauto.
Qed.

Lemma ack_loadE rl kI kR kS ok γ n t :
  store_key rl kI kR kS ok γ -∗
  ctx -∗
  pterm (TEnc kS (Spec.tag (N.@"ack_load") (Spec.of_list [TInt n; t]))) -∗
  ▷ (pterm t ∗
     if ok then version_frag γ n t else True%I).
Proof.
iIntros "#key #(_ & _ & _ & ? & _)".
iApply store_predE_gen; eauto.
Qed.

End Defs.

Arguments storeG Σ : clear implicits.
