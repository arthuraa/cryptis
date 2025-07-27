From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces coGset.
From iris.algebra Require Import agree auth csum gset gmap excl frac numbers.
From iris.algebra Require Import max_prefix_list.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import ticket_lock.
From cryptis Require Import lib term gmeta nown.
From cryptis Require Import cryptis primitives tactics role.
From cryptis Require Import saved_prop.
From cryptis.examples Require Import iso_dh.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Notation connN := (nroot.@"conn").

Record state := State {
  cs_si   :> sess_info;
  cs_ts   :  loc;
  cs_chan :  val;
  cs_role :  role;
}.

Definition cs_share cs := si_share_of (cs_role cs) cs.

#[global]
Instance cs_repr : Repr state :=
  λ s, (#(cs_ts s), si_key s, cs_chan s, repr (cs_role s))%V.

Definition countR := authR max_natUR.
Definition channelR := authR (max_prefix_listUR termO).

Class connGS Σ := ConnGS {
  connGS_count  : inG Σ countR;
  connGS_channel : inG Σ channelR;
  connGS_pred : savedPredG Σ (list term * list term);
}.

Local Existing Instance connGS_count.
Local Existing Instance connGS_channel.
Local Existing Instance connGS_pred.

Definition connΣ := #[
  GFunctor countR;
  GFunctor channelR;
  savedPredΣ (list term * list term)
].

Global Instance subG_connGS Σ : subG connΣ Σ → connGS Σ.
Proof. solve_inG. Qed.

Record params Σ := Params {
  chan_inv :
    sign_key → sign_key → sess_info → list term → list term → iProp Σ;
  msg_inv :
    sign_key → sign_key → sess_info → role → term → iProp Σ;
}.

Section Defs.

Context `{!cryptisGS Σ, !heapGS Σ, !connGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (cs : state).
Implicit Types (kS t : term) (ts : list term).
Implicit Types (skI skR : sign_key).
Implicit Types n m : nat.
Implicit Types b : bool.
Implicit Types v : val.
Implicit Types (ok : Prop) (failed : bool).
Implicit Types (si : sess_info) (rl : role).
Implicit Types (ps : params Σ).

Definition failure skI skR : iProp :=
   public skI ∨ public skR.

Definition wf_sess_info si : iProp :=
  minted (si_key si) ∗
  session si.

#[global]
Instance wf_sess_info_persistent si : Persistent (wf_sess_info si).
Proof. apply _. Qed.

Definition never_connected skI skR : iProp :=
  term_token skR (↑connN.@"server".@skI).

Lemma never_connected_switch skI skR Q : ⊢ switch (never_connected skI skR) Q.
Proof. apply term_token_switch. Qed.

Local Notation chanN := (iso_dhN.@"res".@"chan").
Local Notation recvN := (chanN.@"recv").
Local Notation sentN := (chanN.@"sent").
Local Notation predN := (chanN.@"pred").

Definition recv_count gb rl n : iProp :=
  term_own gb (recvN.@rl) (●{#1/2} MaxNat n).

Lemma recv_count_update gb rl n :
  recv_count gb rl n -∗
  recv_count gb rl n ==∗
  recv_count gb rl (S n) ∗
  recv_count gb rl (S n).
Proof.
iIntros "auth1 auth2". iCombine "auth1 auth2" as "auth".
iMod (term_own_update with "auth") as "[auth frag]".
{ apply: (auth_update_alloc _ _ (MaxNat (S n))).
  apply: max_nat_local_update => /=; lia. }
iDestruct "auth" as "[auth1 auth2]". by iFrame.
Qed.

Lemma recv_count_alloc gb rl E :
  ↑recvN.@rl ⊆ E →
  term_token gb E ==∗
  recv_count gb rl 0 ∗ recv_count gb rl 0 ∗
  term_token gb (E ∖ ↑recvN.@rl).
Proof.
iIntros "% token".
iMod (term_own_alloc (recvN.@rl) (● MaxNat 0)
       with "token") as "[[own1 own2] token]" => //.
- by rewrite auth_auth_valid.
- by iFrame.
Qed.

Definition sent_list gb rl ts : iProp :=
  term_own gb (sentN.@rl) (●{#1/2} to_max_prefix_list ts).

Definition sent_count gb rl n : iProp := ∃ ts,
  ⌜length ts = n⌝ ∧
  term_own gb (sentN.@rl) (●{#1/2} to_max_prefix_list ts).

Definition sent_at gb rl t n : iProp := ∃ ts,
  ⌜length ts = n⌝ ∧
  term_own gb (sentN.@rl) (◯ to_max_prefix_list (ts ++ [t])).

Lemma sent_update t gb rl ts n :
  sent_count gb rl n  -∗
  sent_list gb rl ts ==∗
  sent_count gb rl (S n) ∗
  sent_list gb rl (ts ++ [t]) ∗
  sent_at gb rl t n.
Proof.
iIntros "(%ts' & <- & auth1) auth2".
iCombine "auth1 auth2" gives %->%auth_auth_dfrac_op_inv%(inj _)%leibniz_equiv.
iCombine "auth1 auth2" as "auth".
iMod (term_own_update with "auth") as "[auth frag]".
{ apply: auth_update_alloc.
  trans (to_max_prefix_list ts, to_max_prefix_list ts).
  - rewrite -{3}[to_max_prefix_list ts]left_id.
    exact: core_id_local_update.
  - apply: (max_prefix_list_local_update _ (ts ++ [t])).
    by exists [t]. }
iDestruct "auth" as "[auth1 auth2]". iFrame.
rewrite length_app /=. iModIntro. iSplit => //. iPureIntro. lia.
Qed.

Lemma sent_alloc gb rl E :
  ↑sentN.@rl ⊆ E →
  term_token gb E ==∗
  sent_count gb rl 0 ∗ sent_list gb rl [] ∗
  term_token gb (E ∖ ↑sentN.@rl).
Proof.
iIntros "% token".
iMod (term_own_alloc (sentN.@rl) (● to_max_prefix_list [])
       with "token") as "[[own1 own2] token]" => //.
- by rewrite auth_auth_valid.
- by iFrame.
Qed.

Definition chan gb rl ts : iProp := ∃ ts',
  sent_list gb rl (ts' ++ ts) ∗
  recv_count gb (swap_role rl) (length ts').

Definition chan_inv_for ps skI skR si rl ts_send ts_recv : iProp :=
  chan_inv ps skI skR si
    (if rl is Init then ts_send else ts_recv)
    (if rl is Init then ts_recv else ts_send).

Definition chan_ctx ps skI skR si rl : iProp := ∃ ts_send ts_recv,
  chan (si_resp_share si) rl ts_send ∗
  chan (si_resp_share si) (swap_role rl) ts_recv ∗
  chan_inv_for ps skI skR si rl ts_send ts_recv.

Definition counters ps skI skR si rl n m : iProp :=
  sent_count (si_resp_share si) rl n ∗
  recv_count (si_resp_share si) rl m ∗
  inv connN (chan_ctx ps skI skR si rl).

Lemma chan_send t gb rl n ts :
  sent_count gb rl n -∗
  chan  gb rl ts ==∗
  sent_count gb rl (S n) ∗
  chan gb rl (ts ++ [t]) ∗
  sent_at gb rl t n.
Proof.
iIntros "sent_count (%ts' & sent & recv)".
iMod (sent_update t with "sent_count sent") as "(sent_count & sent & #sent_at)".
rewrite -(assoc app).
by iFrame "sent_count sent recv".
Qed.

Lemma chan_recv t gb rl n ts :
  chan gb rl ts -∗
  sent_at gb rl t n -∗
  recv_count gb (swap_role rl) n ==∗
  ⌜ts = t :: drop 1 ts⌝ ∗
  chan gb rl (drop 1 ts) ∗
  recv_count gb (swap_role rl) (S n).
Proof.
iIntros "(%ts1 & sent & recv1) (%ts2 & <- & frag) recv2".
iCombine "recv1 recv2" gives %e%auth_auth_dfrac_op_inv_L%(f_equal max_nat_car).
iCombine "sent frag"
  gives %(_ & (suf & e_suf)%to_max_prefix_list_included_L
          & _)%auth_both_dfrac_valid_discrete.
rewrite /= in e.
have ?: ts1 = ts2.
  by rewrite -[LHS](take_app_length ts1 ts) e_suf -app_assoc e take_app_length.
subst ts2. move/(f_equal (drop (length ts1))): e_suf.
rewrite -app_assoc !drop_app_length /= => ->.
iMod (recv_count_update with "recv1 recv2") as "[recv1 recv2]".
rewrite /= drop_0.
iFrame. iModIntro. iSplit => //=. iExists (ts1 ++ [t]).
rewrite -app_assoc /= length_app Nat.add_comm. by iFrame.
Qed.

Lemma chan_alloc ps skI skR si :
  term_token (si_resp_share si) (↑chanN) -∗
  chan_inv ps skI skR si [] [] ={⊤}=∗
  inv connN (chan_ctx ps skI skR si Init) ∗
  recv_count (si_resp_share si) Init 0 ∗
  recv_count (si_resp_share si) Resp 0 ∗
  sent_count (si_resp_share si) Init 0 ∗
  sent_count (si_resp_share si) Resp 0.
Proof.
iIntros "tok I".
iMod (@recv_count_alloc _ Init with "tok") as "(rI & rI' & tok)";
  first solve_ndisj. iFrame "rI'".
iMod (@recv_count_alloc _ Resp with "tok") as "(rR & rR' & tok)";
  first solve_ndisj. iFrame "rR'".
iMod (@sent_alloc _ Init with "tok") as "(sI' & sI & tok)";
  first solve_ndisj. iFrame "sI'".
iMod (@sent_alloc _ Resp with "tok") as "(sR' & sR & tok)";
  first solve_ndisj. iFrame "sR'".
iAssert (chan _ Init []) with "[sI rR]" as "cI".
{ iExists []. by iFrame. }
iAssert (chan _ Resp []) with "[sR rI]" as "cR".
{ iExists []. by iFrame. }
iApply (inv_alloc connN ⊤ (chan_ctx ps skI skR si Init) with "[$cI $cR I]").
by iApply "I".
Qed.

Lemma counters_alloc ps skI skR si :
  term_token (si_resp_share si) (↑chanN) -∗
  chan_inv ps skI skR si [] [] ={⊤}=∗
  counters ps skI skR si Init 0 0 ∗
  counters ps skI skR si Resp 0 0.
Proof.
iIntros "tok inv".
iMod (chan_alloc ps skI skR si with "tok inv") as "(#inv & ? & ? & ? & ?)".
iFrame. iFrame "#". iModIntro.
iApply (inv_iff with "inv").
iIntros "!> !>".
by iSplit; iIntros "(%ts_send & %ts_recv & ? & ? & ?)"; iFrame.
Qed.

Lemma counters_send ps skI skR si rl n m t :
  counters ps skI skR si rl n m -∗
  (∀ ts_send ts_recv,
      ▷ chan_inv_for ps skI skR si rl ts_send ts_recv ={⊤ ∖ ↑connN}=∗
      ▷ chan_inv_for ps skI skR si rl (ts_send ++ [t]) ts_recv) ={⊤}=∗
  sent_at (si_resp_share si) rl t n ∗
  counters ps skI skR si rl (S n) m.
Proof.
iIntros "(sent & recv & #inv) upd".
iInv connN as "(%ts_send & %ts_recv & >chan & >chan' & ctx)".
iPoseProof ("upd" with "ctx") as ">ctx".
iMod (chan_send t with "sent chan") as "(? & ? & ?)".
by iFrame.
Qed.

Lemma counters_recv ps skI skR si rl n m t :
  counters ps skI skR si rl n m -∗
  sent_at (si_resp_share si) (swap_role rl) t m -∗
  (∀ ts_send ts_recv,
      ▷ chan_inv_for ps skI skR si rl ts_send (t :: ts_recv) ={⊤ ∖ ↑connN}=∗
      ▷ chan_inv_for ps skI skR si rl ts_send ts_recv ∗
      ▷ msg_inv ps skI skR si rl t) ={⊤}=∗
  counters ps skI skR si rl n (S m) ∗
  ▷ msg_inv ps skI skR si rl t.
Proof.
iIntros "(sent & recv & #inv) #sent_at upd".
iInv connN as "(%ts_send & %ts_recv & >chan & >chan' & ctx)".
rewrite -[in recv_count _ rl _](swap_roleK rl).
iMod (chan_recv t with "chan' sent_at recv") as "(-> & chan' & recv)".
rewrite swap_roleK. iPoseProof ("upd" with "ctx") as ">[ctx inv_t]".
by iFrame.
Qed.

Definition conn_msg_pred kS t : iProp :=
  ∃ si rl n t',
    let rl' := TInt (if rl is Init then 1 else 0) in
    ⌜kS = si_key si⌝ ∗
    ⌜t = Spec.of_list [rl'; TInt n; t']⌝ ∗
    public t' ∗
    sent_at (si_resp_share si) rl t' n.

Definition connected ps skI skR rl cs : iProp :=
  ⌜si_init cs = skI⌝ ∗
  ⌜si_resp cs = skR⌝ ∗
  ⌜cs_role cs = rl⌝ ∗
  channel (cs_chan cs) ∗
  wf_sess_info cs ∗
  ∃ n m, cs_ts cs ↦∗ [ #n; #m ] ∗
    (public (si_key cs) ∨ counters ps skI skR cs rl n m).

Lemma connected_channel ps skI skR rl cs :
  connected ps skI skR rl cs -∗
  channel (cs_chan cs).
Proof. by iIntros "(_ & _ & _ & ? & _)". Qed.

Lemma connected_public_key ps skI skR rl cs :
  connected ps skI skR rl cs -∗
  release_token (si_share_of rl cs) -∗
  public (si_key cs) -∗
  ◇ compromised cs.
Proof.
iIntros "conn rel #p_k".
iPoseProof "conn" as "(_ & _ & <- & _ & #sess & _)".
iDestruct "sess" as "(#? & #sess)".
by iApply (session_compromised with "[] [//] rel").
Qed.

Lemma connected_public_key_or ps skI skR rl cs P :
  connected ps skI skR rl cs -∗
  release_token (si_share_of rl cs) -∗
  public (si_key cs) ∨ P -∗
  connected ps skI skR rl cs ∗
  release_token (si_share_of rl cs) ∗
  ◇ (compromised cs ∨ P).
Proof.
iIntros "conn rel [#fail|P]"; last by iFrame.
iPoseProof (connected_public_key with "conn rel fail") as "#comp".
iFrame. by iLeft.
Qed.

Lemma connected_released_session ps skI skR rl cs :
  connected ps skI skR rl cs -∗
  □ (▷ released_session cs → public (si_key cs)).
Proof.
iIntros "(_ & _ & _ & _ & #sess & _)".
by iDestruct "sess" as "(_ & ? & sess)".
Qed.

Lemma connected_keyE ps skI skR rl cs :
  connected ps skI skR rl cs -∗
  ⌜skI = si_init cs⌝ ∗ ⌜skR = si_resp cs⌝ ∗ ⌜rl = cs_role cs⌝.
Proof. by iIntros "(-> & -> & -> & _)". Qed.

Lemma connected_ok ps skI skR rl cs :
  connected ps skI skR rl cs -∗
  secret skI -∗
  secret skR -∗
  ◇ session_ok cs.
Proof.
iIntros "(<- & <- & <- & _ & #sess & % & % & _ & _) s_kI s_kR".
iDestruct "sess" as "(m_k & sess)".
by iApply (secret_session with "s_kI s_kR").
Qed.

Lemma session_failed_failure si :
  compromised si  ⊢ failure (si_init si) (si_resp si).
Proof. by iIntros "(#failed & _)". Qed.

Lemma connected_failure ps skI skR rl cs :
  connected ps skI skR rl cs -∗
  release_token (si_share_of rl cs) -∗
  public (si_key cs) -∗
  ◇ failure skI skR.
Proof.
iIntros "conn rel fail".
iPoseProof (connected_keyE with "conn") as "#(-> & -> & _)".
iMod (connected_public_key with "conn rel fail") as "fail".
by iApply (session_failed_failure with "fail").
Qed.

Definition pre_ctx `{!iso_dhGS Σ} : iProp :=
  iso_dh_ctx ∗
  senc_pred connN conn_msg_pred.

Lemma pre_ctx_alloc `{!iso_dhGS Σ} E :
  ↑connN ⊆ E →
  iso_dh_ctx -∗
  seal_pred_token SENC E ==∗
  pre_ctx ∗ seal_pred_token SENC (E ∖ ↑connN).
Proof.
iIntros "% #? tok". iFrame "#". by iApply seal_pred_set.
Qed.

Definition ctx `{!iso_dhGS Σ} N ps : iProp :=
  pre_ctx ∗
  iso_dh_pred N (λ skI skR si rl, counters ps skI skR si rl 0 0).

Lemma ctx_alloc `{!iso_dhGS Σ} N ps E :
  ↑N ⊆ E →
  pre_ctx -∗
  iso_dh_token E ==∗
  ctx N ps ∗ iso_dh_token (E ∖ ↑N).
Proof.
iIntros "% #ctx tok". iFrame "#".
by iApply iso_dh_pred_set.
Qed.

End Defs.

Arguments connGS Σ : clear implicits.
