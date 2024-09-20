From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import reservation_map.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis Require Import role session.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PK.

Context `{!heapGS Σ, !cryptisGS Σ, !sessionGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (rl : role) (t kI kR nI nR sI sR kS : term).

Variable N : namespace.

(** We are going to use the following naming conventions:

- [kI], [kR]: The identities of the initiator of the protocol and of the
  responder.  A nonce used to generate their key pair.

- [nI], [sI]: The private key generated by the initiator, and the corresponding
  key share.  In the case of a traditional NSL protocol, [sI = nI], so the
  private key is actually known to the responder.  In the case of a
  Diffie-Hellman exchange, the two will be different.

- [nR], [sR]: Similar, but for the responder.

- [kS]: A session key generated from the keying material exchanged by the
  parties. *)

Definition corruption kI kR : iProp :=
  public (TKey Dec kI) ∨ public (TKey Dec kR).

Global Instance corruptionC : Comm (⊣⊢) corruption.
Proof. by move=> k k'; rewrite /corruption [(_ ∨ _)%I]comm. Qed.

Global Instance corruption_persistent kI kR :
  Persistent (corruption kI kR).
Proof. apply _. Qed.

Definition in_honest kI kR (T : gset term) : bool :=
  bool_decide (TKey Dec kI ∈ T ∧ TKey Dec kR ∈ T).

(** [readable_by t kI kR] *)
Definition readable_by t kI kR : iProp :=
  □ (corruption kI kR → public t).

#[global]
Instance readable_by_persistent t kI kR : Persistent (readable_by t kI kR).
Proof. apply _. Qed.

Definition secret_of t kI kR : iProp :=
  □ (public t ↔ ▷ corruption kI kR).

#[global]
Instance secret_of_persistent t kI kR : Persistent (secret_of t kI kR).
Proof. apply _. Qed.

Class PK := {
  is_priv_key : term → term → term → iProp;

  mk_key_share : term → term;

  mk_key_share_inj :> Inj (=) (=) mk_key_share;

  mk_key_share_minted :
    ∀ n, minted (mk_key_share n) ⊣⊢ minted n;

  mk_key_share_secret_of :
    ∀ n kI kR, minted n -∗ is_priv_key n kI kR -∗
    secret_of (mk_key_share n) kI kR;

  mk_session_key : role → term → term → term;

  mk_session_key_elem_of :
    ∀ rl1 rl2 n1 n1' n2 s2',
      mk_session_key rl1 n1  (mk_key_share n2) =
      mk_session_key rl2 n1' s2' →
      n1' = n1 ∧ s2' = mk_key_share n2 ∨
      n1' = n2 ∧ s2' = mk_key_share n1;

  mk_session_keyC :
    ∀ nI nR, mk_session_key Init nI (mk_key_share nR) =
             mk_session_key Resp nR (mk_key_share nI);

  mk_session_key_minted :
    ∀ rl t1 t2, minted t1 -∗ minted t2 -∗ minted (mk_session_key rl t1 t2);

  confirmation : role → term → term → term → iProp;

  mk_key_share_impl : val;
  wp_mk_key_share : ∀ E kI kR,
    ↑cryptisN ⊆ E →
    {{{ cryptis_ctx }}}
      mk_key_share_impl #() @ E
    {{{ (n : term), RET (n, mk_key_share n) : val;
        minted n ∗ □ is_priv_key n kI kR ∗
        term_token n ⊤
    }}};

  mk_session_key_impl : role → val;
  wp_mk_session_key : ∀ E rl (n s : term),
    {{{ True }}}
      mk_session_key_impl rl n s @ E
    {{{ RET mk_session_key rl n s : val; True}}};

}.

Context `{!PK}.

Definition init_confirm kI kR : iProp := ∀ nI sR,
  let kS := mk_session_key Init nI sR in
  |==> □ confirmation Init kI kR kS.

Definition resp_confirm kR : iProp := ∀ kI sI nR,
  let kS := mk_session_key Resp nR sI in
  |==> □ confirmation Resp kI kR kS.

Implicit Types ks : term * term.

Definition session_ress rl nI nR ks : iProp :=
  let '(kI, kR) := ks in
  □ confirmation rl kI kR (mk_session_key Init nI (mk_key_share nR)) ∧
  if rl is Init then term_token nI (↑N.@"token".@Resp)
  else True.

Definition session_weak' kI kR t ts T : iProp :=
  ◯H{ts} T ∧
  term_meta t (N.@"success") (kI, kR, ts, T).

#[global]
Instance session_weak'_persistent kI kR t ts T :
  Persistent (session_weak' kI kR t ts T).
Proof. apply _. Qed.

Lemma session_weak'_agree kI1 kI2 kR1 kR2 t ts1 ts2 T1 T2 :
  session_weak' kI1 kR1 t ts1 T1 -∗
  session_weak' kI2 kR2 t ts2 T2 -∗
  ⌜kI1 = kI2 ∧ kR1 = kR2 ∧ ts1 = ts2 ∧ T1 = T2⌝.
Proof.
iIntros "(#hon1 & #meta1) (#hon2 & #meta2)".
iPoseProof (term_meta_agree with "meta1 meta2") as "%e".
case: e => -> -> -> ->. iSplit => //.
Qed.

Definition init_started kI kR sI : iProp :=
  public sI ∨
  ∃ n T nI,
    ⌜sI = mk_key_share nI⌝ ∗
    session_weak' kI kR nI n T ∗
    □ is_priv_key nI kI kR.

Lemma session_weak'_set kI kR t ts T :
  ◯H{ts} T -∗
  term_token t (↑N.@"success") ==∗
  session_weak' kI kR t ts T.
Proof.
iIntros "#hon token".
iSplitR => //.
by iApply term_meta_set.
Qed.

Definition session_weak rl kI kR kS ts T : iProp :=
  ∃ n s, ⌜kS = mk_session_key rl n s⌝ ∗
  session_weak' kI kR n ts T.

#[global]
Instance session_weak_persistent rl kI kR kS ts T :
  Persistent (session_weak rl kI kR kS ts T).
Proof. apply _. Qed.

Definition msg1_pred kR m1 : iProp :=
  ∃ sI kI,
    ⌜m1 = Spec.of_list [sI; TKey Enc kI]⌝ ∧
    public (TKey Enc kI) ∧
    readable_by sI kI kR ∧
    init_started kI kR sI.

Definition resp_accepted kI kR sI sR : iProp :=
  public sI ∨
  ∃ n T n' T' nI nR,
    ⌜n' ≤ n⌝ ∧
    session_weak' kI kR nI n' T' ∧
    session_weak' kI kR nR n  T  ∧
    ⌜sI = mk_key_share nI⌝ ∧
    ⌜sR = mk_key_share nR⌝ ∧
    □ is_priv_key nR kI kR ∧
    □ confirmation Resp kI kR (mk_session_key Init nI (mk_key_share nR)) ∧
    session (N.@"session") Resp nI nR (kI, kR).

Definition resp_waiting kI kR sI nR : iProp :=
  public sI ∗ term_token nR (↑N.@"session") ∨
  ∃ nI,
    ⌜sI = mk_key_share nI⌝ ∧
    session (N.@"session") Resp nI nR (kI, kR) ∧
    □ confirmation Resp kI kR (mk_session_key Init nI (mk_key_share nR)) ∧
    waiting_for_peer (N.@"session") session_ress Resp nI nR (kI, kR).

Definition msg2_pred kI m2 : iProp :=
  ∃ sI sR kR,
    ⌜m2 = Spec.of_list [sI; sR; TKey Enc kR]⌝ ∧
    secret_of sR kI kR ∧
    resp_accepted kI kR sI sR.

Definition init_finished kR sR : iProp :=
  public sR ∨
  ∃ nI nR kI n T,
    session_weak' kI kR nI n T ∧
    session_weak' kI kR nR n T ∧
    ⌜sR = mk_key_share nR⌝ ∧
    □ is_priv_key nI kI kR ∧
    □ is_priv_key nR kI kR ∧
    □ confirmation Init kI kR (mk_session_key Init nI (mk_key_share nR)) ∧
    session (N.@"session") Init nI nR (kI, kR) ∧
    session (N.@"session") Resp nI nR (kI, kR).

Definition msg3_pred := init_finished.

(* TODO: Avoid exposing these instances. *)
Local Existing Instances cryptis_inG cryptisGpreS_maps.

Definition session_key_meta_token rl kI kR kS E : iProp :=
  ∃ nI nR γ,
    ⌜kS = mk_session_key Init nI (mk_key_share nR)⌝ ∗
    session (N.@"session") Init nI nR (kI, kR) ∗
    session (N.@"session") Resp nI nR (kI, kR) ∗
    term_meta nI (N.@"token".@rl) γ ∗
    own γ (reservation_map_token E).

Definition session_key_meta rl kI kR `{Countable L} kS N' (x : L) : iProp :=
  ∃ nI nR γ,
    ⌜kS = mk_session_key Init nI (mk_key_share nR)⌝ ∗
    session (N.@"session") Init nI nR (kI, kR) ∗
    session (N.@"session") Resp nI nR (kI, kR) ∗
    term_meta nI (N.@"token".@rl) γ ∗
    own γ (namespace_map_data N' (to_agree (encode x))).

Lemma mk_session_key_inj nI nR nI' nR' kI kR :
  mk_session_key Init nI  (mk_key_share nR) =
  mk_session_key Init nI' (mk_key_share nR') →
  session (N.@"session") Init nI nR (kI, kR) -∗
  session (N.@"session") Resp nI' nR' (kI, kR) -∗
  ⌜nI' = nI⌝.
Proof.
move=> /mk_session_key_elem_of [] [-> /mk_key_share_inj ->]; first by eauto.
iIntros "sessI sessR".
by iDestruct (session_role_agree with "sessI sessR") as "[]".
Qed.

Definition session_key kI kR kS n T : iProp :=
  ∃ nI nR,
    ⌜kS = mk_session_key Init nI (mk_key_share nR)⌝ ∗
    session_weak' kI kR nI n T ∗
    session_weak' kI kR nR n T ∗
    □ is_priv_key nI kI kR ∗
    □ is_priv_key nR kI kR ∗
    □ confirmation Init kI kR kS ∧
    □ confirmation Resp kI kR kS ∧
    session (N.@"session") Init nI nR (kI, kR) ∗
    session (N.@"session") Resp nI nR (kI, kR).

Global Instance session_key_persistent kI kR kS n T:
  Persistent (session_key kI kR kS n T).
Proof. apply _. Qed.

Lemma session_weak_session_key rl kI1 kI2 kR1 kR2 kS n1 n2 T1 T2 :
  session_weak rl kI1 kR1 kS n1 T1 -∗
  session_key kI2 kR2 kS n2 T2 -∗
  ⌜kI1 = kI2 ∧ kR1 = kR2 ∧ n1 = n2 ∧ T1 = T2⌝.
Proof.
iIntros "(%t1 & %t2 & %e1 & #sess1)".
iIntros "(%nI & %nR & %e2 & #sessI & #sessR & _)".
rewrite e2 in e1.
case/mk_session_key_elem_of: e1 => [] [-> e].
- by iApply (session_weak'_agree with "sess1 sessI").
- by iApply (session_weak'_agree with "sess1 sessR").
Qed.

Lemma session_key_confirmation rl kI kR kS n T :
  session_key kI kR kS n T -∗
  confirmation rl kI kR kS.
Proof.
iIntros "(% & % & % & _ & _ & _ & _ & #? & #? & _)".
by case: rl.
Qed.

Definition pk_auth_ctx : iProp :=
  session_ctx (N.@"session") session_ress ∧
  enc_pred (N.@"m1") msg1_pred ∧
  enc_pred (N.@"m2") msg2_pred ∧
  enc_pred (N.@"m3") msg3_pred.

Lemma pk_auth_alloc E1 E2 E' :
  ↑N ⊆ E1 →
  ↑N ⊆ E2 →
  session_token E1 -∗
  enc_pred_token E2 ={E'}=∗
  pk_auth_ctx ∗
  session_token (E1 ∖ ↑N) ∗
  enc_pred_token (E2 ∖ ↑N).
Proof.
iIntros (sub1 sub2) "t1 t2".
rewrite (session_token_difference (↑N) E1) //. iDestruct "t1" as "[t1 t1']".
iMod (session_alloc (N.@"session") session_ress with "t1")
  as "[#H0 t1]"; try solve_ndisj.
rewrite (enc_pred_token_difference (↑N)) //.
iDestruct "t2" as "[t2 t2']".
iMod (enc_pred_set (N.@"m1") msg1_pred with "t2")
  as "[#H1 t2]"; try solve_ndisj.
iMod (enc_pred_set (N.@"m2") msg2_pred with "t2")
  as "[#H2 t2]"; try solve_ndisj.
iMod (enc_pred_set (N.@"m3") msg3_pred with "t2")
  as "[#H3 t2]"; try solve_ndisj.
iModIntro; iFrame; do !iSplit => //.
Qed.

Global Instance persistent_ctx : Persistent pk_auth_ctx.
Proof. apply _. Qed.

End PK.
