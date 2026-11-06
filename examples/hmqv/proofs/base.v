From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import reservation_map.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib.
From cryptis.lib Require Import gmeta nown saved_prop.
From cryptis Require Import cryptis primitives tactics role.
From cryptis.lib Require Import dh hmqv.
From cryptis.examples.hmqv Require Import impl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * HMQV: shared definitions

    This file defines the main concepts used in the specification of the HMQV
    protocol:

    - [sess_info]: a record type containing all the information pertaining to
      an established session.  Parties are identified by their long-term
      public keys.

    - [session_of rl si]: the session [si] was computed by a party with role
      [rl], either [Init] or [Resp].

    - [session_of_key_inj]: a session created by a party is uniquely determined
      by its key, hence by the parties' long-term and ephemeral keys.

    - [hmqv_pred N φ ρ]: the usage [N] of the protocol.  [φ si rl] is what the
      party with role [rl] receives from its peer in [si], and [ρ si] releases
      the key of [si].  To create these assertions, use the [hmqv_token]
      resources provided when the protocol's ghost state is initialized (cf.
      [hmqvGS_alloc]).

    - [compromised rl si]: when the role [rl] completed [si], it could not rule
      out a forged authenticator.

    - [session ρ rl si]: the confidentiality of the key of [si] from the point
      of view of [rl].  Releasing the session publishes its key.  If [si] is
      compromised, its key is public and the peer's long-term private key
      leaked, if the peer's long-term key is honest.  Otherwise [si] is never
      compromised, and its key is public only if released.  Ephemeral private
      keys are deleted right away, so they never leak.

*)

Definition hash_result (tag : string) (val : term) : term :=
  THash (Spec.tag (Tag $ hmqvN.@tag) val).

Lemma gNX : negb (is_exp g). Proof. by []. Qed.
Lemma gNm : negb (is_gmul g). Proof. by []. Qed.

Lemma tags : "init"%string ≠ "resp"%string. Proof. by []. Qed.
Lemma tags' : "resp"%string ≠ "init"%string. Proof. by []. Qed.

Lemma TExp_g_inj (p p' : nonce) : TExp g p = TExp g p' → p = p'.
Proof. by move/(TExp_injr (Ngmul_neq_unit gNm)) => - [] ->. Qed.

#[local] Lemma TExp_g_neq_one (p : nonce) : TExp g p ≠ one.
Proof. exact: Ngmul_neq_unit (Ngmul_TExp _ _ gNm). Qed.

Record sess_info := SessInfo {
  si_init : term;          (* the initiator's long-term public key *)
  si_resp : term;          (* the responder's long-term public key *)
  si_init_share : term;    (* the initiator's ephemeral public key *)
  si_resp_share : term;    (* the responder's ephemeral public key *)
  si_secret : term;        (* the HMQV group element *)
}.

Definition si_share_of rl :=
  if rl is Init then si_init_share
  else si_resp_share.

#[global] Instance sess_info_inhabited : Inhabited sess_info :=
  populate (SessInfo inhabitant inhabitant
              inhabitant inhabitant inhabitant).

(** A role's view of a session: its own keys are honest, its peer's are
    whatever came off the network. *)
Definition init_si (p_a x_a : nonce) P_b X_b : sess_info :=
  SessInfo (TExp g p_a) P_b (TExp g x_a) X_b
    (hmqv_K hmqvN "init" "resp" p_a x_a (TExp g p_a) (TExp g x_a) P_b X_b).

Definition resp_si P_a X_a (p_b x_b : nonce) : sess_info :=
  SessInfo P_a (TExp g p_b) X_a (TExp g x_b)
    (hmqv_K hmqvN "resp" "init" p_b x_b (TExp g p_b) (TExp g x_b) P_a X_a).

Lemma init_resp_si (p_a x_a p_b x_b : nonce) :
  init_si p_a x_a (TExp g p_b) (TExp g x_b)
  = resp_si (TExp g p_a) (TExp g x_a) p_b x_b.
Proof. by rewrite /init_si /resp_si hmqv_K_sym. Qed.

(* A role accepts a session only if neither the peer's long-term key nor the
   HMQV element is the identity. *)
Definition init_session si : Prop :=
  ∃ p_a x_a P_b X_b, si = init_si p_a x_a P_b X_b ∧
    P_b ≠ one ∧ si_secret si ≠ one.

Definition resp_session si : Prop :=
  ∃ P_a X_a p_b x_b, si = resp_si P_a X_a p_b x_b ∧
    P_a ≠ one ∧ si_secret si ≠ one.

Definition session_of rl si : Prop :=
  if rl is Init then init_session si else resp_session si.

Lemma init_session_vetted (p_a x_a p_b : nonce) X_b :
  init_session (init_si p_a x_a (TExp g p_b) X_b).
Proof.
exists p_a, x_a, (TExp g p_b), X_b.
split; first done.
split; first exact: TExp_g_neq_one.
exact: hmqv_K_neq_unit gNX gNm.
Qed.

Lemma resp_session_vetted (p_a : nonce) X_a (p_b x_b : nonce) :
  resp_session (resp_si (TExp g p_a) X_a p_b x_b).
Proof.
exists (TExp g p_a), X_a, p_b, x_b.
split; first done.
split; first exact: TExp_g_neq_one.
exact: hmqv_K_neq_unit gNX gNm.
Qed.

Definition si_key si : senc_key :=
  SEncKey (hash_result "key" (Spec.of_list [si_secret si])).
Arguments si_key : simpl never.

Lemma si_key_inj si1 si2 :
  si_key si1 = si_key si2 → si_secret si1 = si_secret si2.
Proof.
rewrite /si_key => - [] /Spec.tag_inj [] _ /Spec.of_list_inj [].
by [].
Qed.

#[local] Lemma init_si_inj (p_a x_a : nonce) P_b X_b (p_a' x_a' : nonce)
    P_b' X_b' :
  P_b ≠ one → P_b' ≠ one → si_secret (init_si p_a x_a P_b X_b) ≠ one →
  si_key (init_si p_a x_a P_b X_b) = si_key (init_si p_a' x_a' P_b' X_b') →
  init_si p_a x_a P_b X_b = init_si p_a' x_a' P_b' X_b'.
Proof.
move=> nP nP' nK /si_key_inj; rewrite /init_si /= => eK.
have [-> [-> [-> ->]]] := hmqv_K_inj gNX gNm tags nP nP' nK eK.
by [].
Qed.

#[local] Lemma resp_si_inj P_a X_a (p_b x_b : nonce) P_a' X_a'
    (p_b' x_b' : nonce) :
  P_a ≠ one → P_a' ≠ one → si_secret (resp_si P_a X_a p_b x_b) ≠ one →
  si_key (resp_si P_a X_a p_b x_b) = si_key (resp_si P_a' X_a' p_b' x_b') →
  resp_si P_a X_a p_b x_b = resp_si P_a' X_a' p_b' x_b'.
Proof.
move=> nP nP' nK /si_key_inj; rewrite /resp_si /= => eK.
have [-> [-> [-> ->]]] := hmqv_K_inj gNX gNm tags' nP nP' nK eK.
by [].
Qed.

(** ISO-DH's [session_agree], restricted to the sessions a role can build. *)
Lemma session_of_key_inj rl si1 si2 :
  session_of rl si1 → session_of rl si2 →
  si_key si1 = si_key si2 → si1 = si2.
Proof.
case: rl => /=.
- move=> [? [? [? [? [-> [nP nK]]]]]] [? [? [? [? [-> [nP' _]]]]]].
  exact: init_si_inj nP nP' nK.
- move=> [? [? [? [? [-> [nP nK]]]]]] [? [? [? [? [-> [nP' _]]]]]].
  exact: resp_si_inj nP nP' nK.
Qed.

Class hmqvGpreS Σ := HmqvGPreS {
  #[local] hmqvGpreS_meta :: metaGS Σ;
  #[local] hmqvGpreS_pred :: savedPredG Σ (sess_info * option role);
}.

Class hmqvGS Σ := HmqvGS {
  #[local] hmqv_inG :: hmqvGpreS Σ;
  hmqv_name : gname;
}.

Definition hmqvΣ := #[
  metaΣ;
  savedPredΣ (sess_info * option role)
].

#[global] Instance subG_hmqvGpreS Σ : subG hmqvΣ Σ → hmqvGpreS Σ.
Proof. solve_inG. Qed.

Section Verif.

Context `{!heapGS Σ, !cryptisGS Σ, !hmqvGS Σ}.
Abbreviation iProp := (iProp Σ).

Implicit Types (rl : role) (t : term).
Implicit Types (p_a p_b x_a x_b : nonce).
Implicit Types (si : sess_info).
Implicit Types (N : namespace) (E : coPset).
Implicit Types (φ : sess_info → role → iProp).
Implicit Types (ρ : sess_info → iProp).

Lemma wp_H (c : string) (val : list term) Ψ :
  Ψ (repr (hash_result c (Spec.of_list val))) ⊢
  WP H c (repr val) {{ Ψ }}.
Proof.
iIntros "post". wp_lam.
wp_apply wp_term_of_list.
wp_apply wp_tag.
wp_apply wp_hash.
by iApply "post".
Qed.

Lemma wp_session_key σ (Ψ : val → iProp) :
  Ψ (SEncKey (hash_result "key" (Spec.of_list [σ])) : term) ⊢
  WP session_key σ {{ Ψ }}.
Proof.
iIntros "post". wp_lam. wp_list. wp_apply wp_H.
by wp_apply wp_derive_senc_key.
Qed.

Lemma minted_hash_result tag t : minted (hash_result tag t) ⊣⊢ minted t.
Proof. by rewrite /hash_result minted_THash minted_tag. Qed.

Lemma hmqv_key_public (p : nonce) : hmqv_key p -∗ public (TExp g p).
Proof.
iIntros "[#m_p #pred_p]".
have Nm : negb (is_mul (TNonce p)) by [].
iApply (public_dh_share gNX gNm Nm with "[] m_p pred_p").
by rewrite public_TInt.
Qed.

Lemma wp_mk_lt_key :
  {{{ cryptis_ctx }}}
    mk_lt_key #()
  {{{ (p : nonce), RET (TNonce p, TExp g p)%V;
      hmqv_key p ∗ secret p ∗ public (TExp g p) ∗ term_token (TExp g p) ⊤ }}}.
Proof.
iIntros "%Φ #ctx post".
wp_lam.
iMod pending_alloc as (γ) "pend".
wp_apply (wp_mk_nonce_freshN ∅ (λ _, shot γ 1)%I dh_key_share
            (λ x, {[TExp g x]})) => //.
- by iIntros "% %contra".
- iIntros "%x"; rewrite big_sepS_singleton; iModIntro; iSplit.
  + iIntros "#?"; by iApply all_minted_TExp; iSplit => //; iApply minted_TInt.
  + rewrite (minted_TExp x) //; by iIntros "[_ ?]".
iIntros "%p _ #m_p #s_p #pred_p _ tok".
rewrite big_sepS_singleton.
iAssert (□ (public p ↔ ▷ shot γ 1))%I as "#s_p'".
{ iModIntro; iSplit.
  - iIntros "#p". iDestruct ("s_p" with "p") as "#s". iNext.
    by iDestruct "s" as "#s".
  - iIntros "#s". iApply "s_p". iNext. by iModIntro. }
iPoseProof (secret_alloc with "s_p' pend") as "s".
iAssert (hmqv_key p) as "#key"; first by iSplit.
wp_pures. wp_apply wp_texp. wp_pures.
iApply "post". iFrame. iModIntro. iSplit => //. by iApply hmqv_key_public.
Qed.

Definition hmqv_token E : iProp :=
  gmeta_token hmqv_name E.

(* One saved predicate holds a usage's gifts, at [Some rl], and its release
   condition, at [None]. *)
Definition hmqv_pred N φ ρ : iProp :=
  nown hmqv_name N
    (saved_pred DfracDiscarded (λ '(si, o),
       if o is Some rl then φ si rl else ρ si)).

Lemma hmqv_pred_set N φ ρ E :
  ↑N ⊆ E →
  hmqv_token E ==∗ hmqv_pred N φ ρ ∗ hmqv_token (E ∖ ↑N).
Proof. by iIntros "%"; iApply nown_alloc. Qed.

Lemma hmqv_token_difference E1 E2 :
  E1 ⊆ E2 →
  hmqv_token E2 ⊣⊢ hmqv_token E1 ∗ hmqv_token (E2 ∖ E1).
Proof. exact: gmeta_token_difference. Qed.

Lemma hmqv_token_drop E1 E2 :
  E1 ⊆ E2 →
  hmqv_token E2 -∗ hmqv_token E1.
Proof. exact: gmeta_token_drop. Qed.

#[local] Lemma hmqv_pred_agree N φ ρ φ' ρ' :
  hmqv_pred N φ ρ -∗
  hmqv_pred N φ' ρ' -∗
  (∀ si rl, ▷ (φ si rl ≡ φ' si rl)) ∗ (∀ si, ▷ (ρ si ≡ ρ' si)).
Proof.
iIntros "#N1 #N2".
iPoseProof (nown_valid_2 with "N1 N2") as "#valid".
iPoseProof (saved_pred_op_validI with "valid") as "[_ #e]".
iSplit.
- iIntros (si rl). iApply ("e" $! (si, Some rl)).
- iIntros (si). iApply ("e" $! (si, None)).
Qed.

(** The resource a party escrows for its peer, redeemable once with the
    [ready] slice of the peer's share token. *)
Definition hmqv_ready N si rl : iProp := ∀ φ ρ,
  hmqv_pred N φ ρ →
  term_token (si_share_of rl si) (↑hmqvN.@"ready") ={⊤}=∗
    ▷ φ si rl.

Lemma hmqv_ready_alloc N si rl φ ρ :
  hmqv_pred N φ ρ -∗
  φ si rl ={⊤}=∗
  □ hmqv_ready N si rl.
Proof.
iIntros "#N_φ φ_ts".
iMod (escrowI nroot with "φ_ts []") as "#?".
{ by iApply (term_token_switch (si_share_of rl si) (hmqvN.@"ready")). }
iIntros "!> !>  %φ' %ρ' #N_φ' ready".
iDestruct (hmqv_pred_agree with "N_φ N_φ'") as "[#φ_eq _]".
iSpecialize ("φ_eq" $! si rl).
iMod (escrowE with "[//] ready") as "res" => //.
iIntros "!> !>". by iRewrite -"φ_eq".
Qed.

Lemma minted_si_key si : minted (si_secret si) -∗ minted (si_key si).
Proof.
iIntros "#m". rewrite /si_key minted_senc.
iApply minted_hash_result. iApply minted_of_list => /=.
by do !iSplit => //.
Qed.

Lemma public_si_key si : public (si_secret si) -∗ public (si_key si).
Proof.
iIntros "#p". rewrite /si_key public_senc_key.
iApply public_THash; iLeft; iApply public_tag.
iApply public_of_list => /=. by do !iSplit => //.
Qed.

(** The protocol keeps the [hmqvN] part of the token of an ephemeral's share;
    the rest goes to the caller. *)
Lemma wp_mk_ephemeral (Ψ : val → iProp) :
  cryptis_ctx -∗
  (∀ x : nonce,
      ephemeral x -∗ public (TExp g x) -∗
      term_token (TExp g x) (↑hmqvN.@"ready") -∗
      term_token (TExp g x) (↑hmqvN.@"usage") -∗
      term_token (TExp g x) (↑hmqvN.@"compromised") -∗
      term_token (TExp g x) (⊤ ∖ ↑hmqvN) -∗
      Ψ (TNonce x)) -∗
  WP mk_nonce #() {{ Ψ }}.
Proof.
iIntros "#ctx post".
iAssert (public g) as "#p_g"; first by rewrite public_TInt.
wp_apply (wp_mk_nonce_freshN ∅ (λ _, False)%I dh_key_share
            (λ x, {[TExp g x]})) => //.
- by iIntros "% %contra".
- iIntros "%x"; rewrite big_sepS_singleton; iModIntro; iSplit.
  + iIntros "#?"; by iApply all_minted_TExp; iSplit => //; iApply minted_TInt.
  + rewrite (minted_TExp x) //; by iIntros "[_ ?]".
iIntros "%x _ #m_x #s_x #pred_x _ tok".
rewrite big_sepS_singleton.
have Nm_x : negb (is_mul (TNonce x)) by [].
iAssert (ephemeral x) as "#eph".
{ iSplit; first by iSplit. iIntros "!>". iSplit.
  - iIntros "#p". iDestruct ("s_x" with "p") as "#f". iNext.
    by iDestruct "f" as "#[]".
  - iIntros "#f". iApply "s_x". iNext. by iDestruct "f" as "[]". }
iDestruct (term_token_difference _ (↑hmqvN) with "tok") as "[tok_N tok]";
  first done.
iDestruct (term_token_difference _ (↑hmqvN.@"ready") with "tok_N")
  as "[tok_ready tok_N]"; first solve_ndisj.
iDestruct (term_token_difference _ (↑hmqvN.@"usage") with "tok_N")
  as "[tok_usage tok_N]"; first solve_ndisj.
iDestruct (term_token_difference _ (↑hmqvN.@"compromised") with "tok_N")
  as "[tok_comp _]"; first solve_ndisj.
iApply ("post" with "eph [] tok_ready tok_usage tok_comp tok").
by iApply (public_dh_share gNX gNm Nm_x with "p_g m_x pred_x").
Qed.

(** The responder records the usage of a session on its share, where the hash
    predicate of the key finds the release condition. *)
Definition usage X N : iProp :=
  term_meta X (hmqvN.@"usage") N.

Definition si_static rl :=
  if rl is Init then si_init else si_resp.

(** When [rl] completed [si], it could not rule out a forged authenticator. *)
Definition compromised rl si : iProp :=
  term_meta (si_share_of rl si) (hmqvN.@"compromised") true.

#[global] Instance compromised_persistent rl si :
  Persistent (compromised rl si).
Proof. apply _. Qed.

#[global] Instance compromised_timeless rl si :
  Timeless (compromised rl si).
Proof. apply _. Qed.

(** The private key behind [P], if [P] is honest, leaked. *)
Definition leaked P : iProp :=
  ∀ p : nonce, ⌜P = TExp g p⌝ → hmqv_key p → ◇ public p.

(* The second later comes from finding the release condition through the
   usage of the session. *)
Definition session ρ rl si : iProp :=
  minted (si_key si) ∗
  □ (▷ □ ρ si → public (si_key si)) ∗
  (compromised rl si ∗ public (si_key si) ∗
     □ leaked (si_static (swap_role rl) si) ∨
   □ (¬ compromised rl si) ∗ □ (public (si_key si) → ▷ ▷ □ ρ si)).

#[global] Instance session_persistent ρ rl si : Persistent (session ρ rl si).
Proof. apply _. Qed.

Lemma session_minted ρ rl si : session ρ rl si -∗ minted (si_key si).
Proof. by iIntros "[? _]". Qed.

Lemma session_release ρ rl si :
  session ρ rl si -∗ □ (▷ □ ρ si → public (si_key si)).
Proof. by iIntros "(_ & ? & _)". Qed.

Lemma session_ok ρ rl si :
  session ρ rl si -∗
  □ (¬ compromised rl si) -∗
  □ (public (si_key si) → ▷ ▷ □ ρ si).
Proof.
iIntros "(_ & _ & [(#c & _)|(_ & #ok)]) #nc"; last done.
by iDestruct ("nc" with "c") as "[]".
Qed.

Lemma session_compromised ρ rl si :
  session ρ rl si -∗
  compromised rl si -∗
  public (si_key si) ∗ □ leaked (si_static (swap_role rl) si).
Proof.
iIntros "(_ & _ & [(_ & #p & #l)|(#nc & _)]) #c"; first by iSplit.
by iDestruct ("nc" with "c") as "[]".
Qed.

(** A secret peer key rules out compromise, whatever happens to the role's own
    long-term key. *)
Lemma secret_session ρ rl si (p : nonce) :
  ⌜si_static (swap_role rl) si = TExp g p⌝ -∗
  hmqv_key p -∗
  secret p -∗
  session ρ rl si -∗
  ◇ □ (¬ compromised rl si).
Proof.
iIntros "%e #key s (_ & _ & [(_ & _ & #l)|(#nc & _)])"; last by iIntros "!> !>".
iMod ("l" $! p with "[//] key") as "#p".
by iDestruct (secret_not_public with "s p") as ">[]".
Qed.

(** Message predicates for the authenticators of the initiator and the
    responder. *)

(* Either role may run the exchange with whatever long-term key it uses for its
   peer; since that key is not the identity, the authenticator binds it all the
   same (cf. [hmqv_K_inj']). *)
Definition m2_pred t : iProp :=
  ∃ P_a X_a (p_b x_b : nonce) N,
    let si := resp_si P_a X_a p_b x_b in
    ⌜t = Spec.of_list [si_secret si; Tag N]⌝ ∗ ⌜P_a ≠ one⌝ ∗
    hmqv_key p_b ∗ ephemeral x_b ∗ usage (TExp g x_b) N ∗
    hmqv_ready N si Init.

Definition m3_pred t : iProp :=
  ∃ (p_a x_a : nonce) P_b X_b N,
    let si := init_si p_a x_a P_b X_b in
    ⌜t = Spec.of_list [si_secret si; Tag N]⌝ ∗ ⌜P_b ≠ one⌝ ∗
    hmqv_key p_a ∗ ephemeral x_a ∗ hmqv_ready N si Resp.

(** The key hash: released sessions publish their key through it. *)
Definition key_pred t : iProp :=
  ∃ si N φ ρ, ⌜t = Spec.of_list [si_secret si]⌝ ∗ ⌜resp_session si⌝ ∗
    usage (si_resp_share si) N ∗ hmqv_pred N φ ρ ∗ □ ρ si.

Definition hmqv_ctx : iProp :=
  hash_pred (hmqvN.@"m2") m2_pred ∗
  hash_pred (hmqvN.@"m3") m3_pred ∗
  hash_pred (hmqvN.@"key") key_pred.

Lemma hmqv_ctx_alloc E :
  ↑hmqvN ⊆ E →
  hash_pred_token E ==∗
  hmqv_ctx ∗ hash_pred_token (E ∖ ↑hmqvN).
Proof.
iIntros "%sub token".
iMod (hash_pred_set (hmqvN.@"m2") m2_pred with "token")
  as "[? token]"; try solve_ndisj. iFrame.
iMod (hash_pred_set (hmqvN.@"m3") m3_pred with "token")
  as "[? token]"; try solve_ndisj. iFrame.
iMod (hash_pred_set (hmqvN.@"key") key_pred with "token")
  as "[? token]"; try solve_ndisj. iFrame.
iApply (hash_pred_token_drop with "token"). solve_ndisj.
Qed.

(** Both ephemerals are honest, so only release can publish the key. *)
Lemma honest_session N φ ρ p_a p_b x_a x_b :
  let si := resp_si (TExp g p_a) (TExp g x_a) p_b x_b in
  hash_pred (hmqvN.@"key") key_pred -∗
  hmqv_pred N φ ρ -∗
  hmqv_key p_a -∗
  hmqv_key p_b -∗
  ephemeral x_a -∗
  ephemeral x_b -∗
  usage (TExp g x_b) N -∗
  minted (si_key si) -∗
  □ (▷ □ ρ si → public (si_key si)) ∗
  □ (public (si_key si) → ▷ ▷ □ ρ si).
Proof.
move=> si.
iIntros "#Hpred #N_φ #key_pa #key_pb #[key_xa s_xa] #[key_xb s_xb] #use #m_k".
have ss : resp_session si := resp_session_vetted p_a (TExp g x_a) p_b x_b.
iSplit; iModIntro.
- iIntros "#rel". rewrite /si_key public_senc_key.
  iApply (public_THashIS with "Hpred [] []").
  + by iEval (rewrite /si_key minted_senc minted_hash_result) in "m_k".
  + iNext; iModIntro; iExists si, N, φ, ρ. by do !iSplit => //.
- iIntros "#p_k".
  iEval (rewrite /si_key public_senc_key) in "p_k".
  iDestruct (public_THashE with "Hpred p_k") as "[p_t | [_ #rel]]".
  + rewrite public_of_list /=.
    iDestruct "p_t" as "[p_σ _]".
    iDestruct (@public_hmqv_K_honest _ _ _ hmqvN g "resp" "init" p_b x_b p_a x_a
                 gNX gNm tags' with "key_pb key_xb key_pa key_xa p_σ")
      as "[[_ #p]|[_ #p]]".
    * iDestruct ("s_xb" with "p") as "f". iNext. by iDestruct "f" as "[]".
    * iDestruct ("s_xa" with "p") as "f". iNext. by iDestruct "f" as "[]".
  + iNext.
    iDestruct "rel" as "(%si' & %N' & %φ' & %ρ' & %e & %ss' & #use' & #N_φ'
                         & #r)".
    have ek : si_key si = si_key si' by rewrite /si_key e.
    have esi := session_of_key_inj (rl := Resp) ss ss' ek.
    subst si'.
    iPoseProof (term_meta_agree with "use use'") as "<-".
    iDestruct (hmqv_pred_agree with "N_φ N_φ'") as "[_ #ρ_eq]".
    iSpecialize ("ρ_eq" $! si).
    iNext. by iRewrite "ρ_eq".
Qed.
End Verif.

Arguments hmqv_ctx_alloc {Σ _ _ _} E.

Lemma hmqvGS_alloc `{!heapGS Σ, !cryptisGS Σ} E :
  ↑hmqvN ⊆ E →
  hmqvGpreS Σ →
  hash_pred_token E ={⊤}=∗ ∃ (H : hmqvGS Σ),
    hmqv_ctx ∗ hmqv_token ⊤ ∗
    hash_pred_token (E ∖ ↑hmqvN).
Proof.
iIntros "% %Hpre token".
iMod gmeta_token_alloc as (γ_meta) "own".
set hmqvGS0 := {| hmqv_inG := Hpre; hmqv_name := γ_meta |} : hmqvGS Σ.
iExists hmqvGS0.
iMod (hmqv_ctx_alloc with "token") as "[#H ?]" => //.
by iFrame.
Qed.

Arguments hmqvGS_alloc {Σ _ _ E}.
Arguments hmqv_pred_set {Σ _} N φ ρ E.
