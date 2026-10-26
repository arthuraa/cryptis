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
      an established session.

    - [session_of rl si]: the session [si] was computed by a party with role
      [rl], either [Init] or [Resp].

    - [session_of_key_inj]: a session created by a party is uniquely determined
      by its key, hence by the parties' long-term and ephemeral keys.

    - [hmqv_pred N φ]: When the parties authenticate under usage [N], they
      should provide and receive resources given [φ].  To create these
      assertions, use the [hmqv_token] resources provided when the protocol's
      ghost state is initialized (cf. [hmqvGS_alloc]).

    - [release_token X]: A resource for compromising session keys. When both
      parties release these tokens, they can make their session key compromised.

    - [session rl p_a p_b si]: This describes the confidentiality of the key of
      the session [si] from the point of view of the role [rl].  Roughly, this
      says that either there was a compromise during the handshake, or the
      session key is public if and only if it was released (cf. above) or if one
      party had all of its keys compromised.  We say that the handshake was
      compromised for [rl] ([compromised rl si]) if the peer's long-term key was
      public when the handshake completed, or both the party's keys were
      compromised then.

*)

Definition hash_result (tag : string) (val : term) : term :=
  THash (Spec.tag (Tag $ hmqvN.@tag) val).

Lemma hash_result_inj (tag1 tag2 : string) t1 t2 :
  hash_result tag1 t1 = hash_result tag2 t2 -> tag1 = tag2 /\ t1 = t2.
Proof.
rewrite /hash_result => - [] /Spec.tag_inj [] /Tag_inj c ->.
by case: (ndot_inj _ _ _ _ c).
Qed.

Lemma gNX : negb (is_exp g). Proof. by []. Qed.
Lemma gNm : negb (is_gmul g). Proof. by []. Qed.

Lemma tags : "init"%string ≠ "resp"%string. Proof. by []. Qed.
Lemma tags' : "resp"%string ≠ "init"%string. Proof. by []. Qed.

Lemma TExp_g_inj (p p' : nonce) : TExp g p = TExp g p' -> p = p'.
Proof. by move/(@TExp_injr g _ _ gNm) => - [] ->. Qed.

Record sess_info := SessInfo {
  si_init : nonce;         (* the initiator's long-term key *)
  si_resp : nonce;         (* the responder's long-term key *)
  si_init_share : term;    (* X_a = g^x_a *)
  si_resp_share : term;    (* X_b = g^x_b *)
  si_secret : term;        (* the HMQV group element *)
}.

Definition si_share_of rl :=
  if rl is Init then si_init_share
  else si_resp_share.

#[global] Instance sess_info_inhabited : Inhabited sess_info :=
  populate (SessInfo inhabitant inhabitant
              inhabitant inhabitant inhabitant).

(** A role's view of a session: its own keys are honest, the peer's
    ephemeral share is whatever came off the network. *)
Definition init_si (p_a x_a p_b : nonce) X_b : sess_info :=
  SessInfo p_a p_b (TExp g x_a) X_b
    (hmqv_K hmqvN "init" "resp" p_a x_a (TExp g p_a) (TExp g x_a)
            (TExp g p_b) X_b).

Definition resp_si (p_a : nonce) X_a (p_b x_b : nonce) : sess_info :=
  SessInfo p_a p_b X_a (TExp g x_b)
    (hmqv_K hmqvN "resp" "init" p_b x_b (TExp g p_b) (TExp g x_b)
            (TExp g p_a) X_a).

Lemma init_resp_si (p_a x_a p_b x_b : nonce) :
  init_si p_a x_a p_b (TExp g x_b) = resp_si p_a (TExp g x_a) p_b x_b.
Proof. by rewrite /init_si /resp_si hmqv_K_sym. Qed.

Definition init_session si : Prop :=
  ∃ p_a x_a p_b X_b, si = init_si p_a x_a p_b X_b.

Definition resp_session si : Prop :=
  ∃ p_a X_a p_b x_b, si = resp_si p_a X_a p_b x_b.

Definition session_of rl si : Prop :=
  if rl is Init then init_session si else resp_session si.

Definition si_key si : senc_key :=
  SEncKey (hash_result "key" (Spec.of_list [si_secret si])).
Arguments si_key : simpl never.

Lemma si_key_inj si1 si2 :
  si_key si1 = si_key si2 → si_secret si1 = si_secret si2.
Proof.
rewrite /si_key => - [] /Spec.tag_inj [] _ /Spec.of_list_inj [].
by [].
Qed.

Lemma init_si_inj (p_a x_a p_b : nonce) X_b (p_a' x_a' p_b' : nonce) X_b' :
  si_key (init_si p_a x_a p_b X_b) = si_key (init_si p_a' x_a' p_b' X_b') →
  init_si p_a x_a p_b X_b = init_si p_a' x_a' p_b' X_b'.
Proof.
move/si_key_inj; rewrite /init_si /= => eK.
have [-> [-> [-> ->]]] :=
  @hmqv_K_inj hmqvN g "init" "resp" p_a x_a p_b p_a' x_a' p_b' X_b X_b'
              gNX gNm tags eK.
by [].
Qed.

Lemma resp_si_inj (p_a : nonce) X_a (p_b x_b : nonce)
                  (p_a' : nonce) X_a' (p_b' x_b' : nonce) :
  si_key (resp_si p_a X_a p_b x_b) = si_key (resp_si p_a' X_a' p_b' x_b') →
  resp_si p_a X_a p_b x_b = resp_si p_a' X_a' p_b' x_b'.
Proof.
move/si_key_inj; rewrite /resp_si /= => eK.
have [-> [-> [-> ->]]] :=
  @hmqv_K_inj hmqvN g "resp" "init" p_b x_b p_a p_b' x_b' p_a' X_a X_a'
              gNX gNm tags' eK.
by [].
Qed.

(** ISO-DH's [session_agree], restricted to the sessions a role can build. *)
Lemma session_of_key_inj rl si1 si2 :
  session_of rl si1 → session_of rl si2 →
  si_key si1 = si_key si2 → si1 = si2.
Proof.
case: rl => /=.
- by move=> [? [? [? [? ->]]]] [? [? [? [? ->]]]] /init_si_inj.
- by move=> [? [? [? [? ->]]]] [? [? [? [? ->]]]] /resp_si_inj.
Qed.

Class hmqvGpreS Σ := HmqvGPreS {
  #[local] hmqvGpreS_meta :: metaGS Σ;
  #[local] hmqvGpreS_pred :: savedPredG Σ (nonce * nonce * sess_info * role);
}.

Class hmqvGS Σ := HmqvGS {
  #[local] hmqv_inG :: hmqvGpreS Σ;
  hmqv_name : gname;
}.

Definition hmqvΣ := #[
  metaΣ;
  savedPredΣ (nonce * nonce * sess_info * role)
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
Implicit Types (φ : nonce → nonce → sess_info → role → iProp).

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
    (saved_pred DfracDiscarded (λ '(p_a, p_b, si, rl), φ p_a p_b si rl)).

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
Definition hmqv_ready N p_a p_b si rl : iProp := ∀ φ,
  hmqv_pred N φ →
  term_token (si_share_of rl si) (↑hmqvN.@"ready") ={⊤}=∗
    ▷ φ p_a p_b si rl.

Lemma hmqv_ready_alloc N p_a p_b si rl φ :
  hmqv_pred N φ -∗
  φ p_a p_b si rl ={⊤}=∗
  □ hmqv_ready N p_a p_b si rl.
Proof.
iIntros "#N_φ φ_ts".
iMod (escrowI nroot with "φ_ts []") as "#?".
{ by iApply (term_token_switch (si_share_of rl si) (hmqvN.@"ready")). }
iIntros "!> !>  %φ' #N_φ' ready".
iPoseProof (nown_valid_2 with "N_φ N_φ'") as "#valid".
iPoseProof (saved_pred_op_validI with "valid") as "[_ #φ_eq]".
iSpecialize ("φ_eq" $! (p_a, p_b, si, rl)).
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

(** A party's whole state leaked: its long-term key and the private key
    behind its share. *)
Definition state_public (p : nonce) X : iProp := public p ∗ exp_public g X.

Definition states_public si : iProp :=
  state_public (si_init si) (si_init_share si) ∨
  state_public (si_resp si) (si_resp_share si).

#[global] Instance states_public_persistent si :
  Persistent (states_public si).
Proof. apply _. Qed.

Definition si_static rl :=
  if rl is Init then si_init else si_resp.

(** From a role's point of view, the peer's authenticator can be forged iff
    the attacker holds the peer's long-term key or the role's whole state. *)
Definition compromised rl si : iProp :=
  public (si_static (swap_role rl) si) ∨
  state_public (si_static rl si) (si_share_of rl si).

#[global] Instance compromised_persistent rl si :
  Persistent (compromised rl si).
Proof. apply _. Qed.

Lemma compromised_static rl si :
  compromised rl si -∗ public (si_init si) ∨ public (si_resp si).
Proof. case: rl; iIntros "[?|[? _]]"; eauto. Qed.

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

Definition session rl p_a p_b si : iProp :=
  ⌜p_a = si_init si⌝ ∗ ⌜p_b = si_resp si⌝ ∗ minted (si_key si) ∗
  □ (▷ released_session si ∨ states_public si → public (si_key si)) ∗
  (compromised rl si ∨
    □ (public (si_key si) → ▷ released_session si ∨ states_public si)).

Lemma session_minted rl p_a p_b si :
  session rl p_a p_b si -∗
  minted (si_key si).
Proof.
by iIntros "(?&?&?&?)".
Qed.

#[global] Instance session_persistent rl p_a p_b si :
  Persistent (session rl p_a p_b si).
Proof. apply _. Qed.

Definition session_ok si : iProp :=
  □ (public (si_key si) ↔ ▷ released_session si ∨ states_public si).

#[global] Instance session_ok_persistent si : Persistent (session_ok si).
Proof. apply _. Qed.

Lemma secret_session rl p_a p_b si :
  secret p_a -∗
  secret p_b -∗
  session rl p_a p_b si -∗
  ◇ session_ok si.
Proof.
iIntros "sI sR (-> & -> & _ & #comp1 & #comp2)".
iDestruct "comp2" as "[#comp2|#comp2]".
- iDestruct (compromised_static with "comp2") as "[c|c]".
  + by iDestruct (secret_not_public with "sI c") as ">[]".
  + by iDestruct (secret_not_public with "sR c") as ">[]".
- iIntros "!> !>". by iSplit.
Qed.

Lemma session_released_session rl p_a p_b si :
  session rl p_a p_b si -∗
  ▷ released_session si -∗
  public (si_key si).
Proof. iIntros "(_ & _ & _ & #H & _) #rel". iApply "H". by iLeft. Qed.

Lemma session_session_ok rl p_a p_b si :
  session rl p_a p_b si -∗
  compromised rl si ∨ session_ok si.
Proof.
iIntros "#(-> & -> & _ & #? & [?|#?])"; eauto. iRight. iModIntro. by iSplit.
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

Definition session_weak rl p_a p_b si : iProp :=
  ⌜p_a = si_init si⌝ ∗ ⌜p_b = si_resp si⌝ ∗ minted (si_key si) ∗
  (compromised rl si ∨ □ (public (si_key si) → ▷ states_public si)).

Lemma unreleased_session_weak rl p_a p_b si :
  session rl p_a p_b si -∗
  □ (¬ released_session si) -∗
  session_weak rl p_a p_b si.
Proof.
iIntros "(-> & -> & #m_k & #s_k1 & #s_k2) #un".
do !iSplit => //. iDestruct "s_k2" as "[s_k2|#s_k2]"; eauto.
iRight. iApply unreleased_key_secrecy => //. iModIntro.
by iSplit; eauto.
Qed.

(** Message predicates for the authenticators of the initiator and the responder. *)

Definition m2_pred t : iProp :=
  ∃ p_a X_a p_b x_b N,
    let si := resp_si p_a X_a p_b x_b in
    ⌜t = Spec.of_list [si_secret si; Tag N]⌝ ∗
    hmqv_key x_b ∗
    hmqv_ready N p_a p_b si Init.

Definition m3_pred t : iProp :=
  ∃ p_a x_a p_b X_b N,
    let si := init_si p_a x_a p_b X_b in
    ⌜t = Spec.of_list [si_secret si; Tag N]⌝ ∗
    hmqv_key x_a ∗
    hmqv_ready N p_a p_b si Resp.

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
  let si := resp_si p_a (TExp g x_a) p_b x_b in
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
have ss : resp_session si by exists p_a, (TExp g x_a), p_b, x_b.
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
    * iRight. iSplit => //. iExists x_b. by iSplit.
    * iLeft. iSplit => //. iExists x_a. by iSplit.
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
    iDestruct "st" as "[[#p_pa (%x & %e & #p_x)]|[#p_pb (%x & %e & #p_x)]]";
      move/TExp_g_inj: e => <-.
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
