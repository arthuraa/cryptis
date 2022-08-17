From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import reservation_map.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics nown.
From cryptis Require Import role session.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PK.

Context `{!heapGS Σ, !cryptisG Σ, !sessionG Σ}.
Notation iProp := (iProp Σ).

Implicit Types (rl : role) (t kI kR nI nR sI sR kS : term).

Variable N : namespace.

Definition pk_auth_init : val :=
  λ: "c" "mk_key_share" "mk_sess_key" "skI" "pkI" "pkR",
  let: "nIsI" := "mk_key_share" #() in
  let: "nI"   := Fst "nIsI" in
  let: "sI"   := Snd "nIsI" in
  let: "m1"   := tenc (N.@"m1") "pkR" (term_of_list ["sI"; "pkI"]) in
  send "c" "m1";;
  bind: "m2"   := tdec (N.@"m2") "skI" (recv "c") in
  bind: "m2"   := list_of_term "m2" in
  list_match: ["sI'"; "sR"; "pkR'"] := "m2" in
  assert: eq_term "sI'" "sI" && eq_term "pkR'" "pkR" in
  let: "k" := "mk_sess_key" "nI" "sR" in
  let: "m3" := tenc (N.@"m3") "pkR" "sR" in
  send "c" "m3";;
  SOME "k".

Definition pk_auth_resp : val :=
  λ: "c" "mk_key_share" "mk_sess_key" "skR" "pkR",
  bind: "m1" := tdec (N.@"m1") "skR" (recv "c") in
  bind: "m1" := list_of_term "m1" in
  list_match: ["sI"; "pkI"] := "m1" in
  bind: "kt" := is_key "pkI" in
  assert: "kt" = repr Enc in
  let: "nRsR" := "mk_key_share" #() in
  let: "nR" := Fst "nRsR" in
  let: "sR" := Snd "nRsR" in
  let: "m2" := tenc (N.@"m2") "pkI" (term_of_list ["sI"; "sR"; "pkR"]) in
  send "c" "m2";;
  bind: "m3" := tdec (N.@"m3") "skR" (recv "c") in
  assert: eq_term "m3" "sR" in
  let: "k" := "mk_sess_key" "nR" "sI" in
  SOME ("pkI", "k").

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
  pterm (TKey Dec kI) ∨ pterm (TKey Dec kR).

Global Instance corruptionC : Comm (⊣⊢) corruption.
Proof. by move=> k k'; rewrite /corruption [(_ ∨ _)%I]comm. Qed.

Global Instance corruption_persistent kI kR :
  Persistent (corruption kI kR).
Proof. apply _. Qed.

Definition in_honest kI kR (T : gset term) : bool :=
  bool_decide (TKey Dec kI ∈ T ∧ TKey Dec kR ∈ T).

(** [readable_by t kI kR] *)
Definition readable_by t kI kR : iProp :=
  □ (corruption kI kR → pterm t).

#[global]
Instance readable_by_persistent t kI kR : Persistent (readable_by t kI kR).
Proof. apply _. Qed.

Definition secret_of t kI kR : iProp :=
  □ (pterm t ↔ ▷ corruption kI kR).

#[global]
Instance secret_of_persistent t kI kR : Persistent (secret_of t kI kR).
Proof. apply _. Qed.

Class PK := {
  is_priv_key : term → term → term → iProp;

  mk_key_share : term → term;

  mk_key_share_inj :> Inj (=) (=) mk_key_share;

  mk_key_share_sterm :
    ∀ n, sterm (mk_key_share n) ⊣⊢ sterm n;

  mk_key_share_secret_of :
    ∀ n kI kR, sterm n -∗ is_priv_key n kI kR -∗
    secret_of (mk_key_share n) kI kR;

  mk_session_key : role → term → term → term;

  mk_session_key_elem_of :
    ∀ rl nI nI' nR nR',
      mk_session_key rl nI  (mk_key_share nR) =
      mk_session_key rl nI' (mk_key_share nR') →
      nI = nI' ∧ nR = nR' ∨ nI = nR' ∧ nR = nI';

  mk_session_keyC :
    ∀ nI nR, mk_session_key Init nI (mk_key_share nR) =
             mk_session_key Resp nR (mk_key_share nI);

  mk_session_key_sterm :
    ∀ rl t1 t2, sterm t1 -∗ sterm t2 -∗ sterm (mk_session_key rl t1 t2);

  confirmation : role → term → term → term → iProp;

  mk_key_share_impl : val;
  wp_mk_key_share : ∀ E kI kR,
    {{{ True }}}
      mk_key_share_impl #() @ E
    {{{ (n : term), RET (n, mk_key_share n) : val;
        sterm n ∗ □ is_priv_key n kI kR ∗
        nonce_meta_token n ⊤
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
  if rl is Init then nonce_meta_token nI (↑N.@"token".@Resp)
  else True.

Definition session_weak' kI kR t ts T : iProp :=
  ◯H{ts} T ∧
  nonce_meta t (N.@"success") (ts, in_honest kI kR T).

#[global]
Instance session_weak'_persistent kI kR t ts T :
  Persistent (session_weak' kI kR t ts T).
Proof. apply _. Qed.

Lemma session_weak'_agree kI kR t ts1 ts2 T1 T2 :
  session_weak' kI kR t ts1 T1 -∗
  session_weak' kI kR t ts2 T2 -∗
  ⌜ts1 = ts2 ∧ T1 = T2⌝.
Proof.
iIntros "(#hon1 & #meta1) (#hon2 & #meta2)".
iPoseProof (term_meta_agree with "meta1 meta2") as "%e".
case: e => -> _. iSplit => //.
by iApply (honest_frag_agree with "hon1 hon2").
Qed.

Definition init_started kI kR sI : iProp :=
  pterm sI ∨
  ∃ n T nI,
    ⌜sI = mk_key_share nI⌝ ∗
    session_weak' kI kR nI n T ∗
    □ is_priv_key nI kI kR.

Lemma session_weak'_set kI kR t ts T :
  ◯H{ts} T -∗
  nonce_meta_token t (↑N.@"success") ==∗
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
    pterm (TKey Enc kI) ∧
    readable_by sI kI kR ∧
    init_started kI kR sI.

Definition resp_accepted kI kR sI sR : iProp :=
  pterm sI ∨
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
  pterm sI ∗ nonce_meta_token nR (↑N.@"session") ∨
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
  pterm sR ∨
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

Definition session_key_meta_token rl kI kR kS E : iProp :=
  ∃ nI nR γ,
    ⌜kS = mk_session_key Init nI (mk_key_share nR)⌝ ∗
    session (N.@"session") Init nI nR (kI, kR) ∗
    session (N.@"session") Resp nI nR (kI, kR) ∗
    nonce_meta nI (N.@"token".@rl) γ ∗
    own γ (reservation_map_token E).

Definition session_key_meta rl kI kR `{Countable L} kS N' (x : L) : iProp :=
  ∃ nI nR γ,
    ⌜kS = mk_session_key Init nI (mk_key_share nR)⌝ ∗
    session (N.@"session") Init nI nR (kI, kR) ∗
    session (N.@"session") Resp nI nR (kI, kR) ∗
    nonce_meta nI (N.@"token".@rl) γ ∗
    own γ (namespace_map_data N' (to_agree (encode x))).

Lemma mk_session_key_inj nI nR nI' nR' kI kR :
  mk_session_key Init nI  (mk_key_share nR) =
  mk_session_key Init nI' (mk_key_share nR') →
  session (N.@"session") Init nI nR (kI, kR) -∗
  session (N.@"session") Resp nI' nR' (kI, kR) -∗
  ⌜nI' = nI⌝.
Proof.
move=> /mk_session_key_elem_of [[<- <-]|[<- <-]]; first by eauto.
iIntros "sessI sessR".
by iDestruct (session_role_agree with "sessI sessR") as "[]".
Qed.

Global Instance session_key_term_meta rl kI kR :
  TermMeta (@session_key_meta rl kI kR) (session_key_meta_token rl kI kR).

Proof.
split.
- move=> *. by apply _.
- move=> *. by apply _.
- move=> *. by apply _.
- move=> L ? ? E t x N' ?.
  iIntros "(%nI & %nR & %γ & -> & #sessI & #sessR & #meta & own)".
  pose (a := namespace_map_data N' (to_agree (encode x))).
  iMod (own_update _ _ a with "own") as "#own".
  { exact: namespace_map_alloc_update. }
  iModIntro. iExists nI, nR, γ. by do 4!iSplit => //.
- move=> L ? ? kS x N' E ?.
  iIntros "(%nI & %nR & %γ & -> & #sessI & #sessR & #meta & own)".
  iIntros "(%nI' & %nR' & %γ' & %e & #sessI' & #sessR' & #meta' & own')".
  iPoseProof (mk_session_key_inj with "sessI sessR'") as "->" => // {e}.
  iPoseProof (term_meta_agree with "meta meta'") as "<-".
  iPoseProof (own_valid_2 with "own own'") as "%valid".
  by case: (namespace_map_disj _ _ _ _ valid).
- move=> L ? ? kS N' x1 x2.
  iIntros "(%nI & %nR & %γ & -> & #sessI & #sessR & #meta & own)".
  iIntros "(%nI' & %nR' & %γ' & %e & #sessI' & #sessR' & #meta' & own')".
  iPoseProof (mk_session_key_inj with "sessI sessR'") as "->" => // {e}.
  iPoseProof (term_meta_agree with "meta meta'") as "<-".
  iCombine "own own'" as "own".
  iPoseProof (own_valid with "own") as "%valid".
  rewrite reservation_map_data_valid /= to_agree_op_valid_L in valid.
  iPureIntro. exact: inj valid.
- move=> kS E1 E2 sub. apply: anti_symm.
  + iIntros "(%nI & %nR & %γ & -> & #sessI & #sessR & #meta & own)".
    rewrite (reservation_map_token_difference _ _ sub).
    iDestruct "own" as "[own1 own2]".
    iSplitL "own1".
    * iExists nI, nR, γ; iFrame; eauto.
    * iExists nI, nR, γ; iFrame; eauto.
  + iIntros "[tok1 tok2]".
    iDestruct "tok1" as "(%nI & %nR & %γ & -> & #sI & #? & #meta & own)".
    iDestruct "tok2" as "(%nI' & %nR' & %γ' & %e & #? & #sR & #meta' & own')".
    iPoseProof (mk_session_key_inj with "sI sR") as "->" => // {e}.
    iPoseProof (term_meta_agree with "meta meta'") as "<-".
    iCombine "own own'" as "own".
    rewrite -(reservation_map_token_difference _ _ sub).
    iExists nI, nR, γ; iFrame; eauto.
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

Lemma session_key_confirmation rl kI kR kS n T :
  session_key kI kR kS n T -∗
  confirmation rl kI kR kS.
Proof.
iIntros "(% & % & % & _ & _ & _ & _ & #? & #? & _)".
by case: rl.
Qed.

Definition ctx : iProp :=
  session_ctx (N.@"session") session_ress ∧
  enc_pred (N.@"m1") msg1_pred ∧
  enc_pred (N.@"m2") msg2_pred ∧
  enc_pred (N.@"m3") msg3_pred.

Lemma pk_auth_alloc E1 E2 E' :
  ↑N ⊆ E1 →
  ↑N ⊆ E2 →
  nown_token session_name E1 -∗
  enc_pred_token E2 ={E'}=∗
  ctx ∗
  nown_token session_name (E1 ∖ ↑N) ∗
  enc_pred_token (E2 ∖ ↑N).
Proof.
iIntros (sub1 sub2) "t1 t2".
rewrite (nown_token_difference (↑N)) //. iDestruct "t1" as "[t1 t1']".
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

Global Instance persistent_ctx : Persistent ctx.
Proof. apply _. Qed.

Lemma pterm_msg1I n T kI kR nI :
  let sI := mk_key_share nI in
  ctx -∗
  session_weak' kI kR nI n T -∗
  sterm nI -∗
  □ is_priv_key nI kI kR -∗
  pterm (TKey Enc kI) -∗
  pterm (TKey Enc kR) -∗
  pterm (TEnc kR (Spec.tag (N.@"m1") (Spec.of_list [sI; TKey Enc kI]))).
Proof.
iIntros "(_ & #m1P & _ & _) #meta #s_nI #p_nI #p_ekI #p_ekR".
iPoseProof (mk_key_share_secret_of with "s_nI p_nI") as "p_sI".
iApply pterm_TEncIS; eauto.
- by iApply pterm_sterm.
- iModIntro. iExists (mk_key_share nI), kI. do !iSplit => //.
  + iIntros "!> #?". iApply "p_sI". by eauto.
  + iRight. by iExists n, T, nI; eauto.
- rewrite sterm_of_list /= mk_key_share_sterm.
  do !iSplit => //. by iApply pterm_sterm.
iIntros "!> #p_dkR". rewrite pterm_of_list /=. do !iSplit => //.
iApply "p_sI". iModIntro. by iRight.
Qed.

Lemma pterm_msg1E kI kR sI :
  ctx -∗
  pterm (TEnc kR (Spec.tag (N.@"m1") (Spec.of_list [sI; TKey Enc kI]))) -∗
  ▷ (sterm sI ∧ pterm (TKey Enc kI) ∧ readable_by sI kI kR ∧
     init_started kI kR sI).
Proof.
iIntros "(_ & #m1P & _ & _) #p_m1".
iPoseProof (pterm_TEncE with "p_m1 m1P") as "{p_m1} [p_m1 | p_m1]".
- iModIntro. rewrite pterm_of_list /=.
  iDestruct "p_m1" as "(? & ? & ? & _)". iSplit => //.
    by iApply pterm_sterm.
  iSplit; eauto.
  iSplit.
    by iIntros "!> ?".
  by iLeft.
- iDestruct "p_m1" as "{m1P} (#m1P & #s_m1 & #p_m1)".
  iModIntro.
  iDestruct "m1P" as "(%sI' & %kI' & %e_m1 & p_pkI & p_sI & accepted)".
  case/Spec.of_list_inj: e_m1 => <- <-.
  rewrite sterm_of_list /=. iDestruct "s_m1" as "(#s_sI & _)".
  do !iSplit => //.
Qed.

Lemma resp_accept dq n T E kI kR sI nR :
  ↑N ⊆ E →
  let kS := mk_session_key Resp nR sI in
  nonce_meta_token nR ⊤ -∗
  resp_confirm kR -∗
  ctx -∗
  ●H{dq|n} T -∗
  □ is_priv_key nR kI kR -∗
  init_started kI kR sI ={E}=∗
  ●H{dq|n} T ∗
  □ confirmation Resp kI kR kS ∗
  session_weak' kI kR nR n T ∗
  session_weak Resp kI kR kS n T ∗
  resp_waiting kI kR sI nR ∗
  resp_accepted kI kR sI (mk_key_share nR).
Proof.
iIntros (?) "%kS token conf (#ctx & _) hon #p_nR #started".
iMod ("conf" $! kI sI nR) as "#conf".
rewrite (term_meta_token_difference _ (↑N.@"session")) //.
iDestruct "token" as "[token_sess token]".
rewrite (term_meta_token_difference _ (↑N.@"success") (_ ∖ _)) //; last first.
  solve_ndisj.
iDestruct "token" as "[token_succ _]".
iMod (session_weak'_set kI kR nR n T with "[#] token_succ") as "#sess".
  by iApply honest_auth_frag.
iDestruct "started" as "[#fail|(%n' & %T' & %nI & -> & #sess' & #p_nI)]".
  iModIntro. iFrame. iSplit; eauto. iSplit => //. iSplit.
    by iExists _, _; eauto.
  iSplitL; iLeft => //.
  by iFrame.
rewrite -mk_session_keyC in @kS *.
iMod (session_begin _ Resp nI nR (kI, kR)
       with "ctx [] token_sess") as "[#sessR waiting]".
- solve_ndisj.
- rewrite /=. by eauto.
iAssert (⌜n' ≤ n ∧ (n ≤ n' → T = T')⌝)%I as "#[%n'n %nn']".
  iDestruct "sess'" as "[hon' _]".
  by iApply (honest_auth_frag_agree with "[hon]").
iPoseProof (honest_auth_frag with "hon") as "#?".
iFrame. iModIntro. iSplit; eauto. iSplit => //. iSplit.
  rewrite mk_session_keyC in @kS *.
  by iExists _, _; eauto.
iSplitL.
  iRight. iExists nI. by eauto.
iRight. iExists n, T, n', T', nI, nR.
by do !iSplit => //.
Qed.

Lemma pterm_msg2I kI kR sI sR :
  ctx -∗
  pterm (TKey Enc kI) -∗
  pterm (TKey Enc kR) -∗
  sterm sI -∗
  readable_by sI kI kR -∗
  sterm sR -∗
  secret_of sR kI kR -∗
  resp_accepted kI kR sI sR -∗
  pterm (TEnc kI (Spec.tag (N.@"m2") (Spec.of_list [sI; sR; TKey Enc kR]))).
Proof.
iIntros "(_ & _ & #? & _) #p_eI #p_eR #s_sI #p_sI #s_sR #p_sR #accepted".
iApply pterm_TEncIS; eauto.
- by iApply pterm_sterm.
- iModIntro. iExists sI, sR, kR. by eauto.
- rewrite sterm_of_list /=. do ![iSplit => //].
  by iApply pterm_sterm.
iIntros "!> #p_dkI". rewrite pterm_of_list /=. do !iSplit => //.
- by iApply "p_sI"; iLeft.
- iApply "p_sR". iModIntro. by iLeft.
Qed.

Lemma pterm_msg2E kI kR sI sR :
  ctx -∗
  secret_of sI kI kR -∗
  pterm (TEnc kI (Spec.tag (N.@"m2") (Spec.of_list [sI; sR; TKey Enc kR]))) -∗
  ▷ (sterm sR ∧ secret_of sR kI kR ∧ resp_accepted kI kR sI sR).
Proof.
iIntros "(_ & _ & #m2P & _) #started #p_m2".
iPoseProof (pterm_TEncE with "p_m2 m2P") as "{p_m2} [p_m2 | p_m2]".
- rewrite pterm_of_list /=.
  iDestruct "p_m2" as "(? & p_sI & p_sR & _ & _)".
  iSpecialize ("started" with "p_sI").
  iModIntro.
  iSplit; first by iApply pterm_sterm.
  iSplit.
    iModIntro. by iSplit; eauto.
  by iLeft.
- iDestruct "p_m2" as "(#p_m2 & #s_m2 & #?)". rewrite sterm_of_list /=.
  iModIntro.
  iDestruct "p_m2" as "(%sI' & %sR' & %kR' & %e_m2 & sRP & ?)".
  iDestruct "s_m2" as "(s_sI & s_sR & _)".
  case/Spec.of_list_inj: e_m2 => <- <- <-.
  do !iSplit => //.
Qed.

Lemma init_finish dq n T E kI kR nI sR :
  let sI := mk_key_share nI in
  let kS := mk_session_key Init nI sR in
  ↑N ⊆ E →
  ctx -∗
  ●H{dq|n} T -∗
  session_weak' kI kR nI n T -∗
  sterm nI -∗
  □ is_priv_key nI kI kR -∗
  secret_of sR kI kR -∗
  resp_accepted kI kR sI sR -∗
  nonce_meta_token nI (⊤ ∖ ↑N.@"success") -∗
  init_confirm kI kR ={E}=∗
  ▷ (●H{dq|n} T ∗
     □ confirmation Init kI kR kS ∗
     session_weak Init kI kR kS n T ∗
     init_finished kR sR ∗
     (corruption kI kR ∨
      session_key_meta_token Init kI kR kS ⊤ ∗
      session_key kI kR kS n T)).
Proof.
iIntros "%sI %kS % (#ctx & _) hon #sess #s_nI #p_nI #p_sR #accepted token confirm".
iMod ("confirm" $! nI sR) as "#confirm".
iAssert (secret_of sI kI kR) as "p_sI".
  by iApply mk_key_share_secret_of.
rewrite (term_meta_token_difference _ (↑N.@"token")) //; last solve_ndisj.
set TK := N.@"token".
iDestruct "token" as "[token_token token]".
rewrite (term_meta_token_difference _ (↑N.@"session") (_ ∖ _)); last first.
  solve_ndisj.
set S := N.@"session".
iDestruct "token" as "[token_sess token]".
rewrite (term_meta_token_difference _ (↑TK.@Init) (↑TK)); last first.
  solve_ndisj.
iDestruct "token_token" as "[token_init token_token]".
rewrite (term_meta_token_difference _ (↑TK.@Resp) (_ ∖ _)); last first.
  solve_ndisj.
iDestruct "token_token" as "[token_resp _]".
iDestruct "accepted" as "[fail|accepted]".
  iPoseProof ("p_sI" with "fail") as "fail'".
  iModIntro. iModIntro. iFrame. iSplit; eauto. iSplit.
    iExists _, _; eauto.
  iSplit; eauto.
  iLeft. iApply "p_sR". by iApply "p_sI".
iDestruct "accepted"
  as "(%n' & %T' & %n'' & %T'' & %nI' & %nR & %n''n' &
       #sess' & #sess'' &
       %e_sI & -> & #p_nR & #accepted & confirmed)".
move/mk_key_share_inj: e_sI => <-.
iDestruct (session_weak'_agree with "sess' sess") as "[-> ->]".
iAssert (⌜n' = n ∧ T = T'⌝)%I as "#[-> <-]".
  iDestruct "sess''" as "[hon' _]".
  iPoseProof (honest_auth_frag_agree with "hon hon'") as "#[%n'n %T'T]".
  iSplit; last by eauto.
  iPureIntro; lia.
iMod (session_begin _ Init nI nR (kI, kR) with "ctx [token_resp] token_sess")
  as "[#sessI _]".
- solve_ndisj.
- by iSplitR.
iMod (own_alloc (reservation_map_token ⊤)) as "(%γ & map)".
  by apply reservation_map_token_valid.
iMod (term_meta_set _ _ γ (TK.@Init) with "token_init") as "#meta" => //.
iModIntro. iModIntro. iFrame. iSplit; eauto. iSplitR.
  by iExists _, _; eauto.
iSplitR.
  iRight. iExists nI, nR, kI, n, T. do !iSplit => //; by eauto.
iRight. iSplitL.
  iExists nI, nR, γ; by eauto.
iExists nI, nR; do !iSplit => //; eauto.
Qed.

Lemma pterm_msg3I kI kR sI sR :
  ctx -∗
  pterm (TKey Enc kR) -∗
  sterm sR -∗
  secret_of sR kI kR -∗
  init_finished kR sR -∗
  pterm (TEnc kR (Spec.tag (N.@"m3") sR)).
Proof.
iIntros "(_ & _ & _ & #p_m3) #p_eR #s_sR #p_sR #finished".
iApply pterm_TEncIS => //.
  by iApply pterm_sterm.
iIntros "!> #p_dkR". iApply "p_sR". by iRight.
Qed.

Lemma pterm_msg3E kI kR sR :
  ctx -∗
  secret_of sR kI kR -∗
  pterm (TEnc kR (Spec.tag (N.@"m3") sR)) -∗
  ▷ init_finished kR sR.
Proof.
iIntros "(_ & _ & _ & #?) #p_sR #p_m3".
iDestruct (pterm_TEncE with "p_m3 [//]") as "{p_m3} [p_m3|p_m3]".
- iDestruct "p_m3" as "[_ p_m3]". by iLeft.
- by iDestruct "p_m3" as "(#p_m3 & _)".
Qed.

Lemma resp_finish E kI kR sI nR n T :
  let sR := mk_key_share nR in
  let kS := mk_session_key Resp nR sI in
  ↑N ⊆ E →
  ctx -∗
  session_weak' kI kR nR n T -∗
  sterm nR -∗
  □ is_priv_key nR kI kR -∗
  init_finished kR sR -∗
  resp_waiting kI kR sI nR ={E}=∗
  ▷ (corruption kI kR ∨
     session_key_meta_token Resp kI kR kS ⊤ ∗
     session_key kI kR kS n T).
Proof.
iIntros "%sR %kS % #(ctx & _) #sess #s_nR #p_nR [#fail|#finished] waiting".
  iPoseProof (mk_key_share_secret_of with "s_nR p_nR") as "p_sR".
  iModIntro. iLeft. by iApply "p_sR".
iDestruct "finished"
  as "(%nI' & %nR' & %kI' & %n' & %T' &
       #sessWI & #sessWR & %e_sR & p_nI & _ & confirmedI & sessI & sessR')".
move/mk_key_share_inj: e_sR => <- {nR'}.
iDestruct "waiting" as "[[#fail token]|waiting]".
  by iDestruct (session_not_ready with "ctx sessR' token") as "[]"; eauto.
iDestruct "waiting" as "(%nI & -> & #sessR & #confirmedR & waiting)".
move: @kS; rewrite -mk_session_keyC => kS.
iPoseProof (session_agree with "sessR sessR'") as "{sessR'} %e" => //.
case: e => <- <-.
iPoseProof (session_weak'_agree with "sessWR sess") as "[-> ->]".
iMod ("waiting" with "[] sessI") as "[_ >finished]".
  solve_ndisj.
iMod (own_alloc (reservation_map_token ⊤)) as "(%γ & map)".
  by apply reservation_map_token_valid.
rewrite /=.
iMod (term_meta_set _ _ γ (N.@"token".@Resp) with "finished")
  as "#meta" => //.
iModIntro. iModIntro. iRight. iSplitL.
  iExists nI, nR, γ. by eauto.
iExists nI, nR. by do !iSplit => //.
Qed.

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None); iFrame.

Lemma wp_pk_auth_init c kI kR dq n T E :
  ↑cryptisN ⊆ E →
  ↑N ⊆ E →
  channel c -∗
  cryptis_ctx -∗
  ctx -∗
  pterm (TKey Enc kI) -∗
  pterm (TKey Enc kR) -∗
  {{{ init_confirm kI kR ∗ ●H{dq|n} T }}}
    pk_auth_init c mk_key_share_impl (mk_session_key_impl Init)
    (TKey Dec kI) (TKey Enc kI) (TKey Enc kR) @ E
  {{{ okS, RET (repr okS);
      ●H{dq|n} T ∗
      if okS is Some kS then
        sterm kS ∗
        □ confirmation Init kI kR kS ∗
        session_weak Init kI kR kS n T ∗
        if in_honest kI kR T then
          session_key_meta_token Init kI kR kS ⊤ ∗
          session_key kI kR kS n T
        else True
      else True }}}.
Proof.
rewrite /pk_auth_init /in_honest bool_decide_decide.
iIntros (??) "#chan_c #ctx #ctx' #p_kI #p_kR %Ψ !> [confirm hon] Hpost".
wp_pures. wp_bind (mk_key_share_impl _).
iApply (wp_mk_key_share _ kI kR) => //.
iIntros "!> %nI (#s_nI & #p_nI & token)".
rewrite (term_meta_token_difference _ (↑N.@"success")); eauto.
iDestruct "token" as "[token_succ token]".
iMod (session_weak'_set kI kR _ _ _ with "[#] token_succ") as "#sess".
  by iApply honest_auth_frag.
wp_pures.
iPoseProof (mk_key_share_secret_of with "s_nI p_nI") as "p_sI".
wp_list. wp_term_of_list. wp_tenc => /=. wp_pures.
wp_bind (send _ _). iApply (wp_send with "[] [#]"); eauto.
  by iApply (pterm_msg1I with "[]"); eauto.
wp_pures. wp_bind (recv _). iApply wp_recv; eauto.
iIntros "%m2 #p_m2". wp_tdec m2; last protocol_failure.
wp_list_of_term m2; last protocol_failure.
wp_list_match => [sI' sR pkR' {m2} ->|_]; last protocol_failure.
wp_eq_term e; last protocol_failure; subst sI'.
wp_eq_term e; last protocol_failure; subst pkR'.
iPoseProof (pterm_msg2E with "[//] [//] [//]")
  as "{p_m2} (s_sR & p_sR & accepted)".
wp_pures.
iMod (init_finish with "ctx' hon sess s_nI p_nI p_sR accepted token confirm")
  as "(hon & #confirmed & #sess_weak & #finished & session)"; eauto.
wp_bind (mk_session_key_impl _ _ _). iApply wp_mk_session_key => //.
iIntros "!> _". wp_pures. wp_tenc. wp_pures. wp_bind (send _ _).
iApply wp_send => //.
  by iApply pterm_msg3I.
case: decide => [[kIP kRP]|_]; last first.
  wp_pures. iApply ("Hpost" $! (Some (mk_session_key Init nI sR))).
  iFrame. iModIntro. iSplit; eauto. by iApply mk_session_key_sterm.
iDestruct "session" as "[[#fail|#fail]|session]".
- iMod (honest_pterm with "ctx hon fail") as "#contra"; eauto; try solve_ndisj.
  wp_pures. iDestruct "contra" as ">[]".
- iMod (honest_pterm with "ctx hon fail") as "#contra"; eauto; try solve_ndisj.
  wp_pures. iDestruct "contra" as ">[]".
wp_pures. iApply ("Hpost" $! (Some (mk_session_key Init nI sR))).
iFrame. iModIntro. iSplit; eauto. by iApply mk_session_key_sterm.
Qed.

Lemma wp_pk_auth_resp c kR dq n T E :
  ↑cryptisN ⊆ E →
  ↑N ⊆ E →
  channel c -∗
  cryptis_ctx -∗
  ctx -∗
  pterm (TKey Enc kR) -∗
  {{{ resp_confirm kR ∗ ●H{dq|n} T }}}
    pk_auth_resp c mk_key_share_impl (mk_session_key_impl Resp)
      (TKey Dec kR) (TKey Enc kR) @ E
  {{{ res, RET (repr res);
      ●H{dq|n} T ∗
      if res is Some (pkI, kS) then
         ∃ kI, ⌜pkI = TKey Enc kI⌝ ∗
               pterm pkI ∗
               sterm kS ∗
               □ confirmation Resp kI kR kS ∗
               session_weak Resp kI kR kS n T ∗
               if in_honest kI kR T then
                session_key_meta_token Resp kI kR kS ⊤ ∗
                session_key kI kR kS n T
               else True
       else True }}}.
Proof.
iIntros (??) "#? #ctx #ctx' #e_kR %Ψ !> [confirm hon] Hpost".
iPoseProof "ctx'" as "(inv & _)".
rewrite /pk_auth_resp; wp_pures.
wp_bind (recv _); iApply wp_recv => //; iIntros (m1) "#Hm1".
wp_tdec m1; last protocol_failure.
wp_list_of_term m1; last protocol_failure.
wp_list_match => [sI pkI {m1} ->|_]; last protocol_failure.
wp_is_key_eq kt kI et; last protocol_failure; subst pkI.
wp_pures.
case: (bool_decide_reflect (_ = repr_key_type Enc)); last protocol_failure.
case: kt => // _.
iDestruct (pterm_msg1E with "[] Hm1")
  as "{Hm1} (s_sI & p_eI & p_sI & started)"; eauto.
wp_pures.
wp_bind (mk_key_share_impl _). iApply (wp_mk_key_share _ kI kR) => //.
iIntros "!> %nR (#s_nR & #p_nR & token)".
iMod (resp_accept with "token confirm [//] hon [//] [//]")
  as "(hon & #confirmed & #? & #sess_weak & waiting & #accepted)" => //.
wp_pures. wp_list; wp_term_of_list. wp_tenc. wp_pures.
iAssert (secret_of (mk_key_share nR) kI kR) as "p_sR".
  by iApply mk_key_share_secret_of.
wp_bind (send _ _). iApply wp_send => //.
  iApply pterm_msg2I; eauto.
  by iApply mk_key_share_sterm.
wp_pures. wp_bind (recv _). iApply wp_recv => //.
iIntros "%m3 #p_m3". wp_tdec m3; last protocol_failure.
wp_eq_term e; last protocol_failure; subst m3.
iPoseProof (pterm_msg3E with "[//] [//] [//]") as "finished".
wp_pures.
iMod (resp_finish with "[] [] [] [] [] waiting") as "session" => //.
case: (decide (TKey Dec kI ∈ T ∧ TKey Dec kR ∈ T)) => [[kIP kRP]|pub]; last first.
  wp_bind (mk_session_key_impl _ _ _). iApply wp_mk_session_key => //.
  iIntros "!> _". wp_pures.
  iApply ("Hpost" $! (Some (TKey Enc kI, mk_session_key Resp nR sI))).
  iModIntro. iFrame. iExists kI.
  rewrite /in_honest bool_decide_decide decide_False //.
  do 3!iSplit => //; eauto.
  by iApply mk_session_key_sterm => //.
iDestruct "session" as "[[#fail|#fail]|session]".
- wp_bind (mk_session_key_impl _ _ _). iApply wp_mk_session_key => //.
  iIntros "!> _".
  iMod (honest_pterm with "ctx hon fail") as "contra"; eauto; try solve_ndisj.
  wp_pures. by iDestruct "contra" as ">[]".
- wp_bind (mk_session_key_impl _ _ _). iApply wp_mk_session_key => //.
  iIntros "!> _".
  iMod (honest_pterm with "ctx hon fail") as "contra"; eauto; try solve_ndisj.
  wp_pures. by iDestruct "contra" as ">[]".
wp_bind (mk_session_key_impl _ _ _). iApply wp_mk_session_key => //.
iIntros "!> _". wp_pures.
iApply ("Hpost" $! (Some (TKey Enc kI, mk_session_key Resp nR sI))).
iModIntro. iFrame. iExists kI.
rewrite /in_honest bool_decide_decide decide_True //.
do 3!iSplit => //; eauto.
by iApply mk_session_key_sterm => //.
Qed.

End PK.
