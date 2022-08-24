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

Definition handshake_done kS ok : iProp := ∃ kI kR kS' ph T,
  ⌜kS = Spec.tag (nroot.@"keys".@"sym") kS'⌝ ∗
  ⌜ok = in_honest kI kR T⌝ ∗
  pk_dh_session_weak N (λ _ _ _ _, True)%I Init kI kR kS' ph T.

#[global]
Instance handshake_done_persistent kS ok :
  Persistent (handshake_done kS ok).
Proof. apply _. Qed.

Definition wf_key kS γ : iProp :=
  □ (∀ kt, pterm (TKey kt kS) -∗ ◇ False) ∗
  □ ∀ kS', ⌜kS = Spec.tag (nroot.@"keys".@"sym") kS'⌝ -∗ ∃ kI kR ph T,
    pk_dh_session_meta N (λ _ _ _ _, True)%I Init kI kR kS' N γ ∗
    pk_dh_session_key N (λ _ _ _ _, True)%I kI kR kS' ph T.

#[global]
Instance wf_key_persistent kS γ : Persistent (wf_key kS γ).
Proof. apply _. Qed.

Lemma handshake_done_session_key kS ok kI kR ph T :
  handshake_done (Spec.tag (nroot.@"keys".@"sym") kS) ok -∗
  pk_dh_session_key N (λ _ _ _ _, True)%I kI kR kS ph T -∗
  ⌜ok = in_honest kI kR T⌝.
Proof.
iIntros "(%kI' & %kR' & %kS' & %ph' & %T' & %e_kS & %e_ok & #weak)".
case/Spec.tag_inj: e_kS => _ <- {kS'}.
iIntros "#key".
by iDestruct (session_weak_session_key with "weak key") as "(<- & <- & <- & <-)".
Qed.

Lemma wf_key_agree kS ok γ γ' :
  handshake_done kS ok -∗
  wf_key kS γ -∗
  wf_key kS γ' -∗
  ⌜γ = γ'⌝.
Proof.
iIntros "(%kI & %kR & %kS' & %ph & %T & -> & %e_ok & #weak)".
iIntros "(_ & #wf1) (_ & #wf2)".
iDestruct ("wf1" with "[//]") as "(%kI1 & %kR1 & %ph1 & %T1 & meta1 & key1)".
iDestruct ("wf2" with "[//]") as "(%kI2 & %kR2 & %ph2 & %T2 & meta2 & key2)".
iDestruct (session_weak_session_key with "weak key1") as "(<- & <- & <- & <-)".
iDestruct (session_weak_session_key with "weak key2") as "(<- & <- & <- & <-)".
by iApply (term_meta_agree with "meta1 meta2").
Qed.

Definition value_auth kS ts t : iProp := ∃ γ,
  version_auth γ (DfracOwn 1) ts t ∗
  wf_key kS γ.

Definition value_frag kS ts t : iProp := ∃ γ,
  version_frag γ ts t ∗
  wf_key kS γ.

Lemma value_auth_frag kS ts t : value_auth kS ts t -∗ value_frag kS ts t.
Proof.
iIntros "(%γ & auth & #key)".
iExists γ. iSplit => //.
by iApply version_auth_frag.
Qed.

Lemma value_auth_update t' kS ts t :
  value_auth kS ts t ==∗ value_auth kS (S ts) t'.
Proof.
iIntros "(%γ & auth & #key)".
iExists γ. iSplitL => //.
by iApply version_update.
Qed.

Lemma value_frag_agree kS ok ts t1 t2 :
  handshake_done kS ok -∗
  value_frag kS ts t1 -∗
  value_frag kS ts t2 -∗
  ⌜t1 = t2⌝.
Proof.
iIntros "#done (%γ1 & #frag1 & #wf1) (%γ2 & #frag2 & #wf2)".
iDestruct (wf_key_agree with "done wf1 wf2") as "<-".
iPoseProof (version_frag_agree with "frag1 frag2") as "%e".
iPureIntro. by apply (leibniz_equiv _ _ e).
Qed.

Definition init_pred kS (m : term) : iProp := ∃ ok,
  handshake_done kS ok ∗
  if ok then value_frag kS 0 (TInt 0)
  else True.

Definition version_pred kS m : iProp := ∃ (n : nat) t ok,
  ⌜m = Spec.of_list [TInt n; t]⌝ ∗
  pterm t ∗
  handshake_done kS ok ∗
  if ok then value_frag kS n t
  else True.

Definition store_pred kS m : iProp := version_pred kS m.

Definition ack_store_pred kS m : iProp := ∃ (n : nat),
  ⌜m = TInt n⌝. (* FIXME: Do we need anything else here? *)

Definition load_pred (kS m : term) : iProp := True.

Definition ack_load_pred kS m : iProp := version_pred kS m.

Definition store_ctx : iProp :=
  enc_pred (N.@"init") init_pred ∗
  enc_pred (N.@"store") store_pred ∗
  enc_pred (N.@"ack_store") ack_store_pred ∗
  enc_pred (N.@"load") load_pred ∗
  enc_pred (N.@"ack_load") ack_load_pred ∗
  pk_dh_ctx N (λ _ _ _ _, True)%I.

Lemma version_predE kS n t :
  version_pred kS (Spec.of_list [TInt n; t]) -∗
  ∃ ok,
    pterm t ∗
    handshake_done kS ok ∗
    if ok then value_frag kS n t else True.
Proof.
iIntros "(%n' & %t' & %ok & %e_kS & #p_t' & #done & #frag)".
case/Spec.of_list_inj: e_kS => /Nat2Z.inj <- <-.
iExists _; eauto.
Qed.

Lemma handshake_done_agree kS γ ok1 ok2 :
  wf_key kS γ -∗
  handshake_done kS ok1 -∗
  handshake_done kS ok2 -∗
  ⌜ok1 = ok2⌝.
Proof.
iIntros "(_ & #impl)".
iIntros "(%kI1 & %kR1 & %kS1 & %ph1 & %T1 & -> & -> & #sess1)".
iIntros "(%kI2 & %kR2 & %kS2 & %ph2 & %T2 & %e_kS & -> & #sess2)".
case/Spec.tag_inj: e_kS => _ <- {kS2}.
iPoseProof ("impl" with "[//]") as "(%kI & %kR & %ph' & %T' & #meta & #key)" => //.
iPoseProof (session_weak_session_key with "sess1 key") as "(<- & <- & <- & <-)".
iPoseProof (session_weak_session_key with "sess2 key") as "(<- & <- & <- & <-)".
by eauto.
Qed.

Lemma version_predE' N' kS ok n t :
  handshake_done kS ok -∗
  (if ok then ∃ γ, wf_key kS γ else True) -∗
  enc_pred N' version_pred -∗
  pterm (TEnc kS (Spec.tag N' (Spec.of_list [TInt n; t]))) -∗
  ▷ (pterm t ∗
     if ok then value_frag kS n t else True).
Proof.
iIntros "#done #key #? #p_m". iSplit.
  iPoseProof (pterm_TEncE with "p_m [//]") as "{p_m} p_m".
  rewrite pterm_of_list /=.
  iDestruct "p_m" as "[(_ & _ & ? & _)|p_m]" => //.
  iDestruct "p_m" as "(#p_m & _)". iModIntro.
  by iDestruct (version_predE with "p_m") as "(%ok' & ? & _)".
case: ok => //. iDestruct "key" as "(%γ & key)".
iPoseProof (pterm_TEncE with "p_m [//]") as "{p_m} p_m".
iDestruct "p_m" as "[(contra & _)|p_m]" => //.
  iDestruct "key" as "[#s_kS _]".
  iDestruct ("s_kS" with "contra") as ">[]".
iDestruct "p_m" as "(#p_m & _)". iModIntro.
iDestruct (version_predE with "p_m")
  as "(%ok & _ & #done' & #frag) {p_m}".
by iPoseProof (handshake_done_agree with "key done done'") as "<-".
Qed.

Lemma store_predE kS ok n t :
  handshake_done kS ok -∗
  (if ok then ∃ γ, wf_key kS γ else True) -∗
  store_ctx -∗
  pterm (TEnc kS (Spec.tag (N.@"store") (Spec.of_list [TInt n; t]))) -∗
  ▷ (pterm t ∗
     if ok then value_frag kS n t else True).
Proof.
iIntros "#key #wf #(_ & #storeP & _) #p_m".
iApply (version_predE' with "key wf storeP p_m").
Qed.

Lemma ack_loadE kS ok n t :
  handshake_done kS ok -∗
  (if ok then ∃ γ, wf_key kS γ else True) -∗
  store_ctx -∗
  pterm (TEnc kS (Spec.tag (N.@"ack_load") (Spec.of_list [TInt n; t]))) -∗
  ▷ (pterm t ∗
     if ok then value_frag kS n t else True%I).
Proof.
iIntros "#key #? #(_ & _ & _ & _ & ? & _)".
iApply version_predE'; eauto.
Qed.

End Defs.

Arguments storeG Σ : clear implicits.
