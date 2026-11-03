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

    - [hmqv_pred N φ]: When the parties authenticate under usage [N], they
      should provide and receive resources given [φ]: [φ si rl] is what the
      party with role [rl] receives from its peer in [si].  To create these
      assertions, use the [hmqv_token] resources provided when the protocol's
      ghost state is initialized (cf. [hmqvGS_alloc]).

    - [release_token X]: A resource for compromising session keys. When both
      parties release these tokens, they can make their session key compromised.

    - [session rl si]: This describes the confidentiality of the key of the
      session [si] from the point of view of the role [rl], once the peer's
      authenticator checked out.  Either the authenticator was forged
      ([compromised rl si]): the key is public and, if the peer's long-term key
      is [vetted], the attacker holds the peer's long-term private key or the
      role's whole state.  Or the session is authentic: the peer is vetted, and
      the key is public if and only if it was released (cf. above) or one
      party had all of its keys compromised ([session_ok si]).

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
  #[local] hmqvGpreS_pred :: savedPredG Σ (sess_info * role);
}.

Class hmqvGS Σ := HmqvGS {
  #[local] hmqv_inG :: hmqvGpreS Σ;
  hmqv_name : gname;
}.

Definition hmqvΣ := #[
  metaΣ;
  savedPredΣ (sess_info * role)
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

Definition hmqv_pred N φ : iProp :=
  nown hmqv_name N
    (saved_pred DfracDiscarded (λ '(si, rl), φ si rl)).

Lemma hmqv_pred_set N φ E :
  ↑N ⊆ E →
  hmqv_token E ==∗ hmqv_pred N φ ∗ hmqv_token (E ∖ ↑N).
Proof. by iIntros "%"; iApply nown_alloc. Qed.

Lemma hmqv_token_difference E1 E2 :
  E1 ⊆ E2 →
  hmqv_token E2 ⊣⊢ hmqv_token E1 ∗ hmqv_token (E2 ∖ E1).
Proof. exact: gmeta_token_difference. Qed.

Lemma hmqv_token_drop E1 E2 :
  E1 ⊆ E2 →
  hmqv_token E2 -∗ hmqv_token E1.
Proof. exact: gmeta_token_drop. Qed.

(** The resource a party escrows for its peer, redeemable once with the
    [ready] slice of the peer's share token. *)
Definition hmqv_ready N si rl : iProp := ∀ φ,
  hmqv_pred N φ →
  term_token (si_share_of rl si) (↑hmqvN.@"ready") ={⊤}=∗
    ▷ φ si rl.

Lemma hmqv_ready_alloc N si rl φ :
  hmqv_pred N φ -∗
  φ si rl ={⊤}=∗
  □ hmqv_ready N si rl.
Proof.
iIntros "#N_φ φ_ts".
iMod (escrowI nroot with "φ_ts []") as "#?".
{ by iApply (term_token_switch (si_share_of rl si) (hmqvN.@"ready")). }
iIntros "!> !>  %φ' #N_φ' ready".
iPoseProof (nown_valid_2 with "N_φ N_φ'") as "#valid".
iPoseProof (saved_pred_op_validI with "valid") as "[_ #φ_eq]".
iSpecialize ("φ_eq" $! (si, rl)).
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

(** [P] is the public key of an honestly generated DH exponent. *)
Definition vetted P : iProp := ∃ p : nonce, ⌜P = TExp g p⌝ ∗ hmqv_key p.

#[global] Instance vetted_persistent P : Persistent (vetted P).
Proof. apply _. Qed.

Lemma hmqv_key_vetted (p : nonce) : hmqv_key p -∗ vetted (TExp g p).
Proof. iIntros "#key". iExists p. by iSplit. Qed.

Lemma exp_public_TExp (p : nonce) : exp_public g (TExp g p) ⊣⊢ public p.
Proof.
iSplit; last by iIntros "#p"; iExists p; iSplit.
by iIntros "(%p' & %e & #p)"; move/TExp_g_inj: e => ->.
Qed.

(** A party's whole state leaked: the private keys behind its long-term key
    [P] and its share [X]. *)
Definition state_public P X : iProp := exp_public g P ∗ exp_public g X.

Definition states_public si : iProp :=
  state_public (si_init si) (si_init_share si) ∨
  state_public (si_resp si) (si_resp_share si).

#[global] Instance states_public_persistent si :
  Persistent (states_public si).
Proof. apply _. Qed.

Definition si_static rl :=
  if rl is Init then si_init else si_resp.

(** The peer's authenticator may have been forged: the key is public and, if
    the peer's long-term key is vetted, the attacker holds its private key or
    the role's whole state. *)
Definition compromised rl si : iProp :=
  public (si_key si) ∗
  □ (vetted (si_static (swap_role rl) si) →
     exp_public g (si_static (swap_role rl) si) ∨
     state_public (si_static rl si) (si_share_of rl si)).

#[global] Instance compromised_persistent rl si :
  Persistent (compromised rl si).
Proof. apply _. Qed.

Lemma compromised_public rl si : compromised rl si -∗ public (si_key si).
Proof. by iIntros "[? _]". Qed.

(* Between honest parties, compromise exposes a long-term private key. *)
Lemma compromised_static rl si (p_a p_b : nonce) :
  si_init si = TExp g p_a → si_resp si = TExp g p_b →
  hmqv_key p_a -∗
  hmqv_key p_b -∗
  compromised rl si -∗
  public p_a ∨ public p_b.
Proof.
move=> e_a e_b; iIntros "#key_a #key_b [_ #comp]".
iAssert (vetted (si_static (swap_role rl) si)) as "#vet".
  by case: rl; rewrite /= ?e_a ?e_b; iApply hmqv_key_vetted.
iAssert (exp_public g (si_init si) ∨ exp_public g (si_resp si))%I
  as "[c|c]".
  by case: rl; iDestruct ("comp" with "vet") as "[?|[? _]]"; eauto.
- iEval (rewrite e_a exp_public_TExp) in "c". by iLeft.
- iEval (rewrite e_b exp_public_TExp) in "c". by iRight.
Qed.

Definition release_token share : iProp :=
  term_token share (↑hmqvN.@"released").

Lemma release_tokenI share E :
  ↑hmqvN.@"released" ⊆ E →
  term_token share E -∗
  release_token share ∗ term_token share (E ∖ ↑hmqvN.@"released").
Proof.
iIntros "% ?"; by rewrite -term_token_difference.
Qed.

Definition released share : iProp :=
  term_meta share (hmqvN.@"released") true.

Lemma release share : release_token share ==∗ released share.
Proof. by apply term_meta_set. Qed.

Definition released_session si : iProp :=
  released (si_init_share si) ∧ released (si_resp_share si).

Lemma unrelease rl si :
  release_token (si_share_of rl si) ==∗ □ ¬ released_session si.
Proof.
iIntros "tok".
iMod (term_meta_set (hmqvN.@"released") false with "tok") as "#un" => //.
iIntros "!> !> [#init #resp]".
iAssert (released (si_share_of rl si)) as "r"; first by case: rl.
by iPoseProof (term_meta_agree with "r un") as "%".
Qed.

Lemma release_token_released_session si rl :
  release_token (si_share_of rl si) -∗
  released_session si -∗
  False.
Proof.
iIntros "token [#init #resp]".
iApply (term_meta_token (L:=bool) with "token"); last by case: rl.
by [].
Qed.

(** An ephemeral is a [secret] of its owner, and its share's token comes cut
    into the slices that the protocol uses. *)
Lemma wp_mk_ephemeral (Ψ : val → iProp) :
  cryptis_ctx -∗
  (∀ x : nonce,
      secret x -∗ hmqv_key x -∗ public (TExp g x) -∗
      release_token (TExp g x) -∗
      term_token (TExp g x) (↑hmqvN.@"ready") -∗
      term_token (TExp g x) (↑hmqvN.@"res") -∗
      term_token (TExp g x) (⊤ ∖ ↑hmqvN) -∗
      Ψ (TNonce x)) -∗
  WP mk_nonce #() {{ Ψ }}.
Proof.
iIntros "#ctx post".
iAssert (public g) as "#p_g"; first by rewrite public_TInt.
iMod pending_alloc as (γ) "pend".
wp_apply (wp_mk_nonce_freshN ∅ (λ _, shot γ 1)%I dh_key_share
            (λ x, {[TExp g x]})) => //.
- by iIntros "% %contra".
- iIntros "%x"; rewrite big_sepS_singleton; iModIntro; iSplit.
  + iIntros "#?"; by iApply all_minted_TExp; iSplit => //; iApply minted_TInt.
  + rewrite (minted_TExp x) //; by iIntros "[_ ?]".
iIntros "%x _ #m_x #s_x #pred_x _ tok".
rewrite big_sepS_singleton.
have Nm_x : negb (is_mul (TNonce x)) by [].
iAssert (□ (public x ↔ ▷ shot γ 1))%I as "#s_x'".
{ iModIntro; iSplit.
  - iIntros "#p". iDestruct ("s_x" with "p") as "#s". iNext.
    by iDestruct "s" as "#s".
  - iIntros "#s". iApply "s_x". iNext. by iModIntro. }
iPoseProof (secret_alloc with "s_x' pend") as "s".
iAssert (hmqv_key x) as "#key_x"; first by iSplit.
iDestruct (release_tokenI with "tok") as "[tok_rel tok]"; first solve_ndisj.
iDestruct (term_token_difference _ (↑hmqvN.@"ready") with "tok")
  as "[tok_ready tok]"; first solve_ndisj.
iDestruct (term_token_difference _ (↑hmqvN.@"res") with "tok")
  as "[tok_res tok]"; first solve_ndisj.
iDestruct (term_token_drop (⊤ ∖ ↑hmqvN) with "tok") as "tok";
  first solve_ndisj.
iApply ("post" with "s key_x [] tok_rel tok_ready tok_res tok").
by iApply (public_dh_share gNX gNm Nm_x with "p_g m_x pred_x").
Qed.

Definition session_ok si : iProp :=
  □ (public (si_key si) ↔ ▷ released_session si ∨ states_public si).

#[global] Instance session_ok_persistent si : Persistent (session_ok si).
Proof. apply _. Qed.

(** What role [rl] keeps once its peer's authenticator checks out: a forgery,
    or an authentic session with a vetted peer. *)
Definition session rl si : iProp :=
  minted (si_key si) ∗
  (compromised rl si ∨ vetted (si_static (swap_role rl) si) ∗ session_ok si).

#[global] Instance session_persistent rl si : Persistent (session rl si).
Proof. apply _. Qed.

Lemma session_minted rl si : session rl si -∗ minted (si_key si).
Proof. by iIntros "[? _]". Qed.

(* Release or a leaked whole state publishes the key. *)
Lemma session_public rl si :
  session rl si -∗
  ▷ released_session si ∨ states_public si -∗
  public (si_key si).
Proof.
iIntros "(_ & [[#p_k _]|[_ #ok]]) #H"; first by [].
by iApply "ok".
Qed.

(* A public key that was not released means compromise. *)
Lemma session_compromised rl si :
  session rl si -∗
  public (si_key si) -∗
  release_token (si_share_of rl si) -∗
  ◇ compromised rl si.
Proof.
iIntros "(_ & [#comp|[_ #ok]]) #p_k rel"; first by iModIntro.
iDestruct ("ok" with "p_k") as "[#rel'|#st]".
  by iDestruct (release_token_released_session with "rel rel'") as ">[]".
iModIntro. iSplit => //. iIntros "!> _".
iDestruct "st" as "[[#P #X]|[#P #X]]"; case: rl => /=.
- iRight. by iSplit.
- by iLeft.
- by iLeft.
- iRight. by iSplit.
Qed.

(* Secret long-term keys rule out compromise. *)
Lemma secret_session rl si (p_a p_b : nonce) :
  si_init si = TExp g p_a → si_resp si = TExp g p_b →
  hmqv_key p_a -∗
  hmqv_key p_b -∗
  secret p_a -∗
  secret p_b -∗
  session rl si -∗
  ◇ session_ok si.
Proof.
move=> e_a e_b.
iIntros "#key_a #key_b s_a s_b (_ & [#comp|[_ #ok]])"; last by iModIntro.
iDestruct (compromised_static rl e_a e_b with "key_a key_b comp") as "[c|c]".
- by iDestruct (secret_not_public with "s_a c") as ">[]".
- by iDestruct (secret_not_public with "s_b c") as ">[]".
Qed.

Lemma unreleased_key_secrecy si :
  □ (¬ released_session si) -∗
  session_ok si -∗
  □ (public (si_key si) → ▷ states_public si).
Proof.
iIntros "#un #s_k !> #p_k".
iDestruct ("s_k" with "p_k") as "[#rel|#st]"; last by iNext.
iNext. by iDestruct ("un" with "rel") as "[]".
Qed.

(** Once both ephemerals are known to stay secret, only release can publish
    the key. *)
Lemma frozen_key_secrecy si :
  □ (¬ released_session si) -∗
  exp_frozen g (si_init_share si) -∗
  exp_frozen g (si_resp_share si) -∗
  session_ok si -∗
  □ (public (si_key si) → ▷ False).
Proof.
iIntros "#un #fr_a #fr_b #s_k !> #p_k".
iDestruct ("s_k" with "p_k") as "[#rel|[[_ #x]|[_ #x]]]".
- iNext. by iApply "un".
- by iApply (exp_frozen_public with "fr_a x").
- by iApply (exp_frozen_public with "fr_b x").
Qed.

(** Message predicates for the authenticators of the initiator and the responder. *)

(* Either role may run the exchange with whatever long-term key it uses for its
   peer; since that key is not the identity, the authenticator binds it all the
   same (cf. [hmqv_K_inj']). *)
Definition m2_pred t : iProp :=
  ∃ P_a X_a (p_b x_b : nonce) N,
    let si := resp_si P_a X_a p_b x_b in
    ⌜t = Spec.of_list [si_secret si; Tag N]⌝ ∗ ⌜P_a ≠ one⌝ ∗
    hmqv_key p_b ∗ hmqv_key x_b ∗ hmqv_ready N si Init.

Definition m3_pred t : iProp :=
  ∃ (p_a x_a : nonce) P_b X_b N,
    let si := init_si p_a x_a P_b X_b in
    ⌜t = Spec.of_list [si_secret si; Tag N]⌝ ∗ ⌜P_b ≠ one⌝ ∗
    hmqv_key p_a ∗ hmqv_key x_a ∗ hmqv_ready N si Resp.

(** The key hash: released sessions publish their key through it. *)
Definition key_pred t : iProp :=
  ∃ si, ⌜t = Spec.of_list [si_secret si]⌝ ∗
        ⌜resp_session si⌝ ∗
        released_session si.

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

(** FIXME: This statement is too cumbersome. *)
Lemma honest_session_ok p_a p_b x_a x_b :
  let si := resp_si (TExp g p_a) (TExp g x_a) p_b x_b in
  hash_pred (hmqvN.@"key") key_pred -∗
  hmqv_key p_a -∗
  hmqv_key p_b -∗
  hmqv_key x_a -∗
  hmqv_key x_b -∗
  minted (si_key si) -∗
  session_ok si.
Proof.
move=> si.
iIntros "#Hpred #key_pa #key_pb #key_xa #key_xb #m_k".
have ss : resp_session si := resp_session_vetted p_a (TExp g x_a) p_b x_b.
iPoseProof (hmqv_key_public with "key_pa") as "#p_Pa".
iPoseProof (hmqv_key_public with "key_pb") as "#p_Pb".
iPoseProof (hmqv_key_public with "key_xa") as "#p_Xa".
iPoseProof (hmqv_key_public with "key_xb") as "#p_Xb".
iModIntro; iSplit.
- iIntros "#p_k".
  iEval (rewrite /si_key public_senc_key) in "p_k".
  iDestruct (public_THashE with "Hpred p_k") as "[p_t | [_ #rel]]".
  + rewrite public_of_list /=.
    iDestruct "p_t" as "[p_σ _]".
    iRight.
    iDestruct (@public_hmqv_K_honest _ _ _ hmqvN g "resp" "init" p_b x_b p_a x_a
                 gNX gNm tags' with "key_pb key_xb key_pa key_xa p_σ")
      as "[[#? #?]|[#? #?]]".
    * iRight. by iSplit; [iExists p_b|iExists x_b]; iSplit.
    * iLeft. by iSplit; [iExists p_a|iExists x_a]; iSplit.
  + iLeft. iNext. iDestruct "rel" as "(%si' & %e & %ss' & #rel')".
    have ek : si_key si = si_key si' by rewrite /si_key e.
    by rewrite (session_of_key_inj (rl := Resp) ss ss' ek).
- iIntros "#[rel|st]".
  + rewrite /si_key public_senc_key.
    iApply (public_THashIS with "Hpred [] []").
    * by iEval (rewrite /si_key minted_senc minted_hash_result) in "m_k".
    * iNext; iModIntro; iExists si.
      by do !iSplit => //.
  + iApply public_si_key. iEval (rewrite /si /=).
    iDestruct "st" as "[[(%p & %e & #p_p) (%x & %e' & #p_x)]|
                        [(%p & %e & #p_p) (%x & %e' & #p_x)]]";
      move/TExp_g_inj: e => <-; move/TExp_g_inj: e' => <-.
    * iEval (rewrite hmqv_K_sym). by iApply public_hmqv_K.
    * by iApply public_hmqv_K.
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
Arguments hmqv_pred_set {Σ _} N φ E.
