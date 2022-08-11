From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis Require Import role session pk_auth pk_dh.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* MOVE *)
#[global]
Instance if_persistent (Σ : gFunctors) (b : bool) (φ ψ : iProp Σ) :
  Persistent φ →
  Persistent ψ →
  Persistent (if b then φ else ψ).
Proof. by case: b. Qed.
(* /MOVE *)

Record cst := {
  cst_ts   : loc;
  cst_key  : term;
  cst_name : gname;
  cst_ok   : bool;
}.

#[local]
Instance cst_repr : Repr cst := λ s, (#(cst_ts s), Spec.mkskey (cst_key s))%V.

(* FIXME: Maybe generalize this *)
Definition sess_recv N : val := λ: "c" "k" "f",
  do_until (λ: <>,
    let: "m" := recv "c" in
    bind: "m" := tsdec N "k" "m" in
    "f" "m"
  ).

Module Client.

Section Client.

Variable N : namespace.

Definition connect : val := λ: "c" "skA" "pkA" "pkB",
  do_until (λ: <>,
    bind: "kS" := pk_dh_init N "c" "skA" "pkA" "pkB" in
    let: "l"  := ref #0 in
    let: "kS" := mkskey (tag (N.@"key") "kS") in
    SOME ("l", "kS")
  ).

Definition get_ts : val := λ: "cs",
  let: "l" := Fst "cs" in
  !"l".

Definition next_ts : val := λ: "cs",
  let: "l" := Fst "cs" in
  "l" <- (!"l" + #1).

Definition get_sk : val := λ: "cs",
  Snd "cs".

Definition send_store : val := λ: "c" "cs" "v",
  next_ts "cs";;
  let: "n" := get_ts "cs" in
  let: "sk" := get_sk "cs" in
  let: "m" := tsenc (N.@"store") "sk" (term_of_list [tint "n"; "v"]) in
  send "c" "m".

Definition ack_store : val := λ: "c" "cs",
  let: "n" := get_ts "cs" in
  let: "sk" := get_sk "cs" in
  sess_recv (N.@"ack_store") "c" "sk" (λ: "m",
    assert: eq_term "m" (tint "n") in
    SOME #()
  ).

Definition store : val := λ: "c" "cs" "t",
  send_store "c" "cs" "t";;
  ack_store "c" "cs".

Definition load : val := λ: "c" "cs",
  let: "n" := tint (get_ts "cs") in
  let: "sk" := get_sk "cs" in
  send "c" (tsenc (N.@"load") "sk" "n");;
  sess_recv (N.@"ack_load") "c" "sk" (λ: "resp",
    bind: "resp" := list_of_term "resp" in
    list_match: ["n'"; "t"] := "resp" in
    assert: eq_term "n'" "n" in
    SOME "t"
  ).

End Client.

End Client.

Record sst := {
  sst_ts  : loc;
  sst_val : loc;
  sst_key : term;
}.

#[global]
Instance repr_sst : Repr sst :=
  λ ss, (#(sst_ts ss), #(sst_val ss), sst_key ss)%V.

Module Server.

Implicit Types N : namespace.

Definition get_ts : val := λ: "ss",
  !(Fst "ss").

Definition set_ts : val := λ: "ss" "ts",
  Fst "ss" <- "ts".

Definition get_val : val := λ: "ss",
  !(Fst (Snd "ss")).

Definition set_val : val := λ: "ss" "v",
  Fst (Snd "ss") <- "v".

Definition get_key : val := λ: "ss",
  Snd (Snd "ss").

Definition handle_store N : val := λ: "c" "ss" "m",
  bind: "m" := list_of_term "m" in
  list_match: ["n"; "x"] := "m" in
  bind: "n'" := to_int "n" in
  assert: get_ts "ss" ≤ "n'" in
  set_ts "ss" "n'";;
  set_val "ss" "v";;
  send "c" (tenc (N.@"ack_store") (get_key "ss") "n").

Definition handle_load N : val := λ: "c" "ss" "m",
  bind: "n" := to_int "m" in
  assert: get_ts "ss" = "n" in
  let: "v" := get_val "ss" in
  send "c" (tsenc (N.@"ack_load") (get_key "ss") (term_of_list ["m"; "v"])).

Definition conn_handler_body N : val := λ: "c" "ss",
  let: "sk" := get_key "ss" in
  let: "m" := recv "c" in
  match: tsdec (N.@"store") "sk" "m" with
    SOME "m" => handle_store N "c" "ss" "m"
  | NONE => match: tsdec (N.@"load") "sk" "m" with
    SOME "m" => handle_load N "c" "ss" "m"
  | NONE => #()
  end end.

Definition conn_handler N : val := rec: "loop" "c" "ss" :=
  conn_handler_body N "c" "ss";;
  "loop" "c" "ss".

Definition listen N : val := rec: "loop" "c" "skB" "pkB" :=
  match: pk_dh_resp N "c" "skB" "pkB" with
    NONE =>
    "loop" "c" "skB" "pkB"
  | SOME "res" =>
    let: "pkA" := Fst "res" in
    let: "kS"  := mkskey (tag (N.@"key") (Snd "res")) in
    let: "ss"  := (ref #0, ref #0, "ks") in
    Fork (conn_handler N "c" "ss");;
    "loop" "c" "skB" "pkB"
  end.

End Server.

Section Verif.

Context `{!cryptisG Σ, !heapGS Σ, !sessionG Σ}.
Notation iProp := (iProp Σ).

Class storeG := StoreG {
  store_inG :> inG Σ (authR (max_prefix_listUR termO));
}.

Context `{!storeG}.

Local Instance STORE : PK := PK_DH (λ _ _ _ _, True)%I.

Implicit Types s : cst.
Implicit Types kI kR kS t : term.
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types cs v : val.

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

Definition cur_term_auth γ n t : iProp := ∃ ts,
  own γ (● to_max_prefix_list (ts ++ [t]) ⋅
         ◯ to_max_prefix_list (ts ++ [t])) ∗
  ⌜n = length ts⌝.

Definition cur_term_frag γ n t : iProp := ∃ ts,
  own γ (◯ to_max_prefix_list (ts ++ [t])) ∗
  ⌜n = length ts⌝.

Lemma cur_term_auth_alloc : ⊢ |==> ∃ γ, cur_term_auth γ 0 (TInt 0).
Proof.
iMod (own_alloc (● to_max_prefix_list [TInt 0] ⋅
                 ◯ to_max_prefix_list [TInt 0])) as "[%γ own]".
  rewrite auth_both_valid_discrete; split; eauto.
  by apply to_max_prefix_list_valid.
iModIntro. iExists γ, []. rewrite /=. iFrame. by eauto.
Qed.

#[global]
Instance cur_term_frag_persistent γ n t : Persistent (cur_term_frag γ n t).
Proof. apply _. Qed.

Lemma cur_term_auth_frag γ n t : cur_term_auth γ n t -∗ cur_term_frag γ n t.
Proof.
iDestruct 1 as "(%ts & [own1 #own2] & %nE)".
iExists ts; eauto.
Qed.

Lemma upd_cur_term γ n t t' :
  cur_term_auth γ n t ==∗ cur_term_auth γ (n + 1) t'.
Proof.
iDestruct 1 as "(%ts & own & ->)".
iMod (own_update with "own") as "own".
  eapply auth_update.
  apply (max_prefix_list_local_update _ ((ts ++ [t]) ++ [t'])).
  by exists [t'].
iModIntro. rewrite plus_comm /=.
iExists (ts ++ [t]). rewrite own_op app_length. iFrame.
iPureIntro. simpl. lia.
Qed.

Definition store_key kI kR kS γ : iProp := ∃ kS',
  ⌜kS = Spec.tag (N.@"key") kS'⌝ ∗
  pk_dh_session_meta N (λ _ _ _ _, True)%I Init kI kR kS' N γ ∗
  □ (∀ kt, pterm (TKey kt kS) -∗ ◇ False).

Definition client_state kI kR s n t : iProp :=
  cst_ts s ↦ #n ∗
  sterm (cst_key s) ∗
  cur_term_auth (cst_name s) n t ∗
  if cst_ok s then store_key kI kR (cst_key s) (cst_name s)
  else True%I.

Lemma client_state_cur_term_frag kI kR s n t :
  client_state kI kR s n t -∗
  cur_term_frag (cst_name s) n t.
Proof.
iIntros "(_ & _ & ? & _)".
by iApply cur_term_auth_frag.
Qed.

Lemma client_state_cst_key kI kR s n t :
  client_state kI kR s n t -∗
  sterm (cst_key s) ∗
  if cst_ok s then store_key kI kR (cst_key s) (cst_name s)
  else True.
Proof. by iIntros "(_ & ? & _ & ?)"; eauto. Qed.

Definition store_pred kS m : iProp := ∃ (n : nat) t kI kR γ,
  ⌜m = Spec.of_list [TInt n; t]⌝ ∗
  cur_term_frag γ n t ∗
  (True ∨ store_key kI kR kS γ). (* FIXME: This is trivial currently *)

Definition ack_store_pred kS m : iProp := ∃ (n : nat),
  ⌜m = TInt n⌝. (* FIXME: Do we need anything else here? *)

Definition load_pred (kS m : term) : iProp := True.

Definition ack_load_pred kS m : iProp := ∃ (n : nat) t,
  ⌜m = Spec.of_list [TInt n; t]⌝ ∗
  ∀ kI kR γ t', store_key kI kR kS γ -∗
  cur_term_frag γ n t' -∗
  ⌜t = t'⌝.

Definition ctx : iProp :=
  enc_pred (N.@"store") store_pred ∗
  enc_pred (N.@"ack_store") ack_store_pred ∗
  enc_pred (N.@"load") load_pred ∗
  enc_pred (N.@"ack_load") ack_load_pred ∗
  pk_dh_ctx N (λ _ _ _ _, True)%I ∗
  key_pred (N.@"key") (λ _ _, False)%I.

Lemma wp_client_get_ts E kI kR s n t :
  {{{ client_state kI kR s n t }}}
    Client.get_ts (repr s) @ E
  {{{ RET #n; client_state kI kR s n t }}}.
Proof.
rewrite /Client.get_ts.
iIntros "%Φ (Hl & #s_kS & Hγ & state) post".
wp_pures. wp_load. iApply "post". iModIntro. by iFrame.
Qed.

Lemma wp_client_next_ts t' E kI kR s n t :
  {{{ client_state kI kR s n t }}}
    Client.next_ts (repr s) @ E
  {{{ RET #(); client_state kI kR s (n + 1) t' }}}.
Proof.
iIntros "%Ψ (n_stored & #s_key & n_t & auth) post".
iMod (upd_cur_term _ _ _ t' with "n_t") as "n_t".
rewrite /Client.next_ts; wp_pures; wp_load; wp_store.
iApply "post"; iFrame.
rewrite (_ : (n + 1)%nat = (n + 1)%Z :> Z); last by lia.
by iFrame.
Qed.

Lemma wp_client_get_sk E kI kR s n t :
  {{{ client_state kI kR s n t }}}
    Client.get_sk (repr s) @ E
  {{{ RET (repr (Spec.mkskey (cst_key s))); client_state kI kR s n t }}}.
Proof.
rewrite /Client.get_sk.
iIntros "%Φ ? post". wp_pures. by iApply "post".
Qed.

Lemma wp_client_send_store E kI kR c s n t t' :
  ↑cryptisN ⊆ E →
  channel c -∗
  ctx -∗
  pterm t' -∗ (* FIXME: t' does not have to be public already *)
  {{{ client_state kI kR s n t }}}
    Client.send_store N c (repr s) t' @ E
  {{{ RET #(); client_state kI kR s (n + 1) t' }}}.
Proof.
rewrite /Client.send_store.
iIntros "% #chan_c (#? & _) #p_t' !> %Φ state post".
wp_pures. wp_bind (Client.next_ts _).
iApply (wp_client_next_ts t' with "state"); iIntros "!> state".
iPoseProof (client_state_cur_term_frag with "state") as "#frag".
wp_pures. wp_bind (Client.get_ts _).
iApply (wp_client_get_ts with "state"); iIntros "!> state".
wp_pures. wp_bind (Client.get_sk _).
iApply (wp_client_get_sk with "state"); iIntros "!> state".
iPoseProof (client_state_cst_key with "state") as "# (s_k & p_k)".
wp_pures. wp_list. wp_bind (tint _). iApply wp_tint. wp_list.
wp_term_of_list. wp_tsenc. wp_pures.
iApply (wp_send with "[//]"); eauto; last by iApply "post".
iModIntro. iApply pterm_TEncIS => //.
- by rewrite sterm_TKey.
- iModIntro. iExists (n + 1), t', kI, kR, (cst_name s).
  rewrite Nat2Z.inj_add /=.
  iSplit => //. iSplit => //. by case: (cst_ok s); eauto.
- rewrite sterm_of_list /= sterm_TInt; do ![iSplit => //].
  by iApply pterm_sterm.
- iModIntro. iIntros "_". rewrite pterm_of_list /= pterm_TInt. iSplit => //.
  by iSplit => //.
Qed.

Lemma wp_client_ack_store E kI kR c s n t :
  ↑cryptisN ⊆ E →
  channel c -∗
  ctx -∗
  {{{ client_state kI kR s n t }}}
    Client.ack_store N c (repr s) @ E
  {{{ RET #(); client_state kI kR s n t }}}.
Proof.
iIntros "% #chan_c (_ & #? & _) !> %Φ state post".
rewrite /Client.ack_store. wp_pures.
wp_bind (Client.get_ts _). iApply (wp_client_get_ts with "state") => //.
iIntros "!> state". wp_pures.
wp_bind (Client.get_sk _). iApply (wp_client_get_sk with "state") => //.
iIntros "!> state". wp_pures.
iPoseProof (client_state_cst_key with "state") as "#[s_k ?]".
iCombine "post state" as "I". iRevert "I".
iApply wp_sess_recv => //. iIntros "!> %m [post state] _".
wp_pures. wp_bind (tint _). iApply wp_tint.
wp_eq_term e; wp_pures; iModIntro; last first.
  iLeft. by iFrame.
iRight. iExists _; iSplit => //. by iApply "post".
Qed.

Lemma wp_client_store E kI kR c s n t t' :
  ↑cryptisN ⊆ E →
  channel c -∗
  ctx -∗
  pterm t' -∗
  {{{ client_state kI kR s n t }}}
    Client.store N c (repr s) t' @ E
  {{{ RET #(); client_state kI kR s (n + 1) t' }}}.
Proof.
iIntros "% #chan_c #ctx #p_t' !> %Φ state post". rewrite /Client.store.
wp_pures. wp_bind (Client.send_store _ _ _ _).
iApply (wp_client_send_store with "[] [] [] [state] [post]") => //.
iIntros "!> state". wp_pures.
iApply (wp_client_ack_store with "[] [] [state] [post]") => //.
Qed.

Lemma wp_client_connect E c kI kR dq T :
  ↑N ⊆ E →
  ↑cryptisN ⊆ E →
  channel c -∗
  cryptis_ctx -∗
  ctx -∗
  pterm (TKey Enc kI) -∗
  pterm (TKey Enc kR) -∗
  {{{ ●H{dq} T }}}
    Client.connect N c (TKey Dec kI) (TKey Enc kI) (TKey Enc kR) @ E
  {{{ s, RET (repr s);
      ●H{dq} T ∗
      ⌜cst_ok s = bool_decide (TKey Dec kI ∈ T ∧ TKey Dec kR ∈ T)⌝ ∗
      client_state kI kR s 0 (TInt 0) }}}.
Proof.
iIntros "% % #chan_c #ctx (_ & _ & _ & _ & #ctx' & #key) #p_ekI #p_ekR".
iIntros "!> %Φ hon post". rewrite /Client.connect. wp_pures.
iCombine "hon post" as "post". iRevert "post".
iApply wp_do_until. iIntros "!> [hon post]". wp_pures.
wp_bind (pk_dh_init _ _ _ _ _).
iApply (wp_pk_dh_init with "[] [] [] [] [] [hon]"); eauto.
  by iFrame.
iIntros "!> %okS [hon HokS]".
case: okS => [kS|]; wp_pures; last by iLeft; iFrame; eauto.
wp_alloc l as "Hl". wp_pures. wp_tag. wp_bind (mkskey _). iApply wp_mkskey.
iMod cur_term_auth_alloc as "[%γ cur_term]".
wp_pures. iRight. iExists _. iSplitR; eauto.
iDestruct "HokS" as "(#s_kS & _ & status)".
set (P := TKey Dec kI ∈ T ∧ TKey Dec kR ∈ T).
iApply ("post" $! {| cst_ts := l; cst_key := Spec.tag (N.@"key") kS;
                     cst_name := γ;
                     cst_ok := bool_decide P |}).
rewrite /client_state /=. iFrame. iSplitR; eauto.
rewrite sterm_tag. iSplitR => //.
rewrite bool_decide_decide; case: decide; last by eauto.
iIntros "%_". iDestruct "status" as "(#p_kS & token & #session)".
iMod (term_meta_set _ _ γ N with "token") as "#meta"; eauto.
iModIntro. iExists kS. do 2!iSplit => //. iIntros "!> %kt #p_kS'".
rewrite (pterm_TKey kt) pterm_tag sterm_tag.
iDestruct "p_kS'" as "[?|[_ p_kS']]"; first by iApply "p_kS".
by iMod (wf_key_elim with "p_kS' key") as "#[]".
Qed.

Lemma wp_client_load E c kI kR s n t :
  ↑N ⊆ E →
  ↑cryptisN ⊆ E →
  channel c -∗
  ctx -∗
  pterm (TKey Enc kI) -∗
  pterm (TKey Enc kR) -∗
  {{{ client_state kI kR s n t }}}
    Client.load N c (repr s) @ E
  {{{ t', RET (repr t');
      client_state kI kR s n t ∗
      ◇ ⌜cst_ok s → t' = t⌝ }}}.
Proof.
iIntros "% % #chan_c #ctx #p_ekI #p_ekR !> %Φ state post".
iDestruct "ctx" as "(_ & _ & ? & ? & _)".
rewrite /Client.load. wp_pures.
wp_bind (Client.get_ts _). iApply (wp_client_get_ts with "state").
iIntros "!> state". wp_pures. wp_bind (tint _). iApply wp_tint.
wp_pures. wp_bind (Client.get_sk _).
iApply (wp_client_get_sk with "state"). iIntros "!> state". wp_pures.
wp_tsenc. wp_pures.
iPoseProof (client_state_cst_key with "state") as "#[s_k status]".
wp_bind (send _ _). iApply wp_send; eauto.
  iModIntro. iApply pterm_TEncIS; eauto.
  - by rewrite sterm_TKey.
  - by rewrite sterm_TInt.
  - rewrite pterm_TInt. by eauto.
wp_pures.
iCombine "post state" as "I". iRevert "I". iApply wp_sess_recv => //.
iIntros "!> %ts [post state] #p_t'". wp_pures.
wp_list_of_term ts; wp_pures; last by iLeft; iFrame.
wp_list_match => [n' v -> {ts}|_]; wp_pures; last by iLeft; iFrame.
wp_eq_term e; wp_pures; last by iLeft; iFrame.
subst n'. iModIntro. iRight. iExists _; iSplit; eauto.
iApply ("post" $! v). iSplit => //.
case e_ok: (cst_ok s) => //=. iIntros "_".
iPoseProof "status" as "(%kS' & %e_kS & #meta & #p_kS)".
iDestruct "p_t'" as "[[contra _] | succ]".
  iMod ("p_kS" $! Enc with "contra") as "{contra} #[]".
iDestruct "succ" as "(_ & #wf_t' & _)".
iDestruct "wf_t'" as "(%n' & %t' & %e & tP)".
iDestruct "state" as "(_ & _ & auth & _)".
case/Spec.of_list_inj: e => /Nat2Z.inj <- <- {n' t'}.
iModIntro.
iApply "tP".
- by iApply "status".
- by iApply cur_term_auth_frag.
Qed.

End Verif.
