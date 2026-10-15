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

    The session record, the long-term key predicate, the predicates of the
    three tagged hashes, and the compromise and release machinery of ISO-DH
    ([examples/iso_dh/proofs/base.v]).  The key algebra comes from
    [cryptis/lib/hmqv.v]. *)

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
Lemma gNi : negb (is_ginv g). Proof. by []. Qed.

Lemma tags : "init"%string ≠ "resp"%string. Proof. by []. Qed.
Lemma tags' : "resp"%string ≠ "init"%string. Proof. by []. Qed.

Lemma TExp_g_inj (p p' : nonce) : TExp g p = TExp g p' -> p = p'.
Proof. by move/(@TExp_injr g _ _ gNm gNi) => - [] ->. Qed.

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
              gNX gNm gNi tags eK.
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
              gNX gNm gNi tags' eK.
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

Lemma _wp_H (tag : string) (val : term) Ψ :
  Ψ (repr (hash_result tag val)) ⊢ WP _H tag val {{ Ψ }}.
Proof.
iIntros "post".
wp_lam.
wp_apply wp_tag.
wp_apply wp_hash.
by iApply "post".
Qed.

Lemma wp_H (tag : string) (val : list term) Ψ :
  Ψ (repr (hash_result tag (Spec.of_list val))) ⊢
  WP H tag (repr val) {{ Ψ }}.
Proof.
iIntros "post".
wp_lam.
wp_apply wp_term_of_list.
by wp_apply _wp_H.
Qed.

Lemma minted_hash_result tag t : minted (hash_result tag t) ⊣⊢ minted t.
Proof. by rewrite /hash_result minted_THash minted_tag. Qed.

(** A long-term key pair [(p, g^p)].  Unlike [dh_seed], [p] may be
    compromised later; all that is fixed is its use as a DH exponent. *)
Definition hmqv_key (p : nonce) : iProp :=
  minted p ∗ □ (∀ t, exp_pred_base p t ↔ ▷ □ dh_key_share t).

#[global] Instance hmqv_key_persistent (p : nonce) : Persistent (hmqv_key p).
Proof. apply _. Qed.

Lemma hmqv_key_public (p : nonce) : hmqv_key p -∗ public (TExp g p).
Proof.
iIntros "[#m_p #pred_p]".
have Nm : negb (is_mul (TNonce p)) by [].
iApply (public_dh_share gNX gNm gNi Nm with "[] m_p pred_p").
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

Definition hmqv_ready N p_a p_b si : iProp := ∀ φ,
  hmqv_pred N φ →
  term_token (si_init_share si) (↑hmqvN.@"ready") ={⊤}=∗
    ▷ φ p_a p_b si Init.

Lemma hmqv_ready_alloc N p_a p_b si φ :
  hmqv_pred N φ -∗
  φ p_a p_b si Init ={⊤}=∗
  □ hmqv_ready N p_a p_b si.
Proof.
iIntros "#N_φ φ_ts".
iMod (escrowI nroot with "φ_ts []") as "#?".
{ by iApply (term_token_switch (si_init_share si) (hmqvN.@"ready")). }
iIntros "!> !>  %φ' #N_φ' ready".
iPoseProof (nown_valid_2 with "N_φ N_φ'") as "#valid".
iPoseProof (saved_pred_op_validI with "valid") as "[_ #φ_eq]".
iSpecialize ("φ_eq" $! (p_a, p_b, si, Init)).
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

Definition compromised si : iProp :=
  (public (si_init si) ∨ public (si_resp si)) ∗
  public (si_key si).

Lemma compromised_public si : compromised si ⊢ public (si_key si).
Proof. by iIntros "(_&?)". Qed.

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

Definition session p_a p_b si : iProp :=
  ⌜p_a = si_init si⌝ ∗ ⌜p_b = si_resp si⌝ ∗ minted (si_key si) ∗
  □ (▷ released_session si → public (si_key si)) ∗
  ((public (si_init si) ∨ public (si_resp si)) ∨
    □ (public (si_key si) → ▷ released_session si)).

Lemma session_minted p_a p_b si :
  session p_a p_b si -∗
  minted (si_key si).
Proof.
by iIntros "(?&?&?&?)".
Qed.

#[global] Instance session_persistent p_a p_b si :
  Persistent (session p_a p_b si).
Proof. apply _. Qed.

Definition session_ok si : iProp :=
  □ (public (si_key si) ↔ ▷ released_session si).

#[global] Instance session_ok_persistent si : Persistent (session_ok si).
Proof. apply _. Qed.

Lemma secret_session p_a p_b si :
  secret p_a -∗
  secret p_b -∗
  session p_a p_b si -∗
  ◇ session_ok si.
Proof.
iIntros "sI sR (-> & -> & _ & #comp1 & #comp2)".
iDestruct "comp2" as "[[comp2|comp2]|comp2]".
- by iDestruct (secret_not_public with "sI comp2") as ">[]".
- by iDestruct (secret_not_public with "sR comp2") as ">[]".
- iIntros "!> !>". by iSplit.
Qed.

Lemma session_released_session p_a p_b si :
  session p_a p_b si -∗
  ▷ released_session si -∗
  public (si_key si).
Proof. iIntros "(_ & _ & _ & #H & _) #rel". by iApply "H". Qed.

Lemma session_session_ok p_a p_b si :
  session p_a p_b si -∗
  (public (si_init si) ∨ public (si_resp si)) ∨ session_ok si.
Proof.
iIntros "#(-> & -> & _ & #? & [?|#?])"; eauto. iRight. iModIntro. by iSplit.
Qed.

Lemma unreleased_key_secrecy si :
  □ (¬ released_session si) -∗
  session_ok si -∗
  □ (public (si_key si) ↔ ▷ False).
Proof.
iIntros "#un #s_k !>".
iApply (bi.iff_trans _ (▷ released_session si)). iSplit => //.
iSplit; last by iIntros ">[]".
iIntros "#re !>". by iApply "un".
Qed.

Definition session_weak p_a p_b si : iProp :=
  ⌜p_a = si_init si⌝ ∗ ⌜p_b = si_resp si⌝ ∗ minted (si_key si) ∗
  ((public p_a ∨ public p_b) ∨ □ (public (si_key si) ↔ ▷ False)).

Lemma unreleased_session_weak p_a p_b si :
  session p_a p_b si -∗
  □ (¬ released_session si) -∗
  session_weak p_a p_b si.
Proof.
iIntros "(-> & -> & #m_k & #s_k1 & #s_k2) #un".
do !iSplit => //. iDestruct "s_k2" as "[s_k2|#s_k2]"; eauto.
iRight. iApply unreleased_key_secrecy => //. iModIntro.
by iSplit; eauto.
Qed.

Lemma release_token_key_secrecy rl si :
  release_token (si_share_of rl si) -∗
  session_ok si -∗
  public (si_key si) -∗
  ▷ False.
Proof.
iIntros "token #s_k #p_k".
iPoseProof ("s_k" with "p_k") as "contra".
iModIntro. by iApply (release_token_released_session with "token").
Qed.

Lemma session_ok_compromised rl si :
  session_ok si -∗
  compromised si -∗
  release_token (si_share_of rl si) -∗
  ▷ False.
Proof.
iIntros "#ok [_ #comp] rel".
iApply (release_token_key_secrecy with "rel ok comp").
Qed.

Lemma session_compromised p_a p_b rl si :
  session p_a p_b si -∗
  public (si_key si) -∗
  release_token (si_share_of rl si) -∗
  ◇ compromised si.
Proof.
iIntros "(-> & -> & _ & #comp1 & #[[comp2|comp2]|#comp2]) #p_k rel".
- iSplit => //. by eauto.
- iSplit => //. by eauto.
- iSpecialize ("comp2" with "p_k").
  iDestruct (release_token_released_session with "rel comp2") as ">[]".
Qed.

Lemma session_compromised' p_a p_b si :
  session p_a p_b si -∗
  compromised si -∗
  public p_a ∨ public p_b.
Proof. by iIntros "(-> & -> & _) (? & _)". Qed.

(** The responder's authenticator vouches for its ephemeral and escrows the
    initiator's resources; [N] is bound as under ISO-DH's signed [m2]. *)
Definition m2_pred t : iProp :=
  ∃ p_a X_a p_b x_b N,
    let si := resp_si p_a X_a p_b x_b in
    ⌜t = Spec.of_list [si_secret si; Tag N]⌝ ∗
    ⌜X_a ≠ TExp g x_b⌝ ∗
    eph_seed x_b ∗
    hmqv_ready N p_a p_b si.

(** The initiator's authenticator vouches for its ephemeral. *)
Definition m3_pred t : iProp :=
  ∃ p_a x_a p_b X_b,
    ⌜t = Spec.of_list [si_secret (init_si p_a x_a p_b X_b)]⌝ ∗
    eph_seed x_a.

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

(** Both roles conclude the same way once they know the peer's share is an
    honest ephemeral: the ephemeral-ephemeral factor keeps the key secret
    whatever happens to the long-term keys, so only release can publish it. *)
Lemma honest_session_ok p_a p_b x_a x_b :
  let si := resp_si p_a (TExp g x_a) p_b x_b in
  x_a ≠ x_b →
  hash_pred (hmqvN.@"key") key_pred -∗
  eph_seed x_a -∗
  eph_seed x_b -∗
  minted (si_key si) -∗
  session_ok si.
Proof.
move=> si x_a_b.
iIntros "#Hpred #eph_a #eph_b #m_k".
have ss : resp_session si by exists p_a, (TExp g x_a), p_b, x_b.
iModIntro; iSplit.
- iIntros "#p_k".
  iEval (rewrite /si_key public_senc_key) in "p_k".
  iDestruct (public_THashE with "Hpred p_k") as "[p_t | [_ #rel]]".
  + rewrite public_of_list /=.
    iDestruct "p_t" as "[p_σ _]".
    iDestruct (@public_hmqv_K_eph _ _ _ hmqvN g "resp" "init" p_b x_b p_a x_a
                 (TExp g p_b) (TExp g x_b) gNX gNm gNi (not_eq_sym x_a_b)
                 with "eph_b eph_a p_σ") as ">[]".
  + iNext. iDestruct "rel" as "(%si' & %e & %ss' & #rel')".
    have ek : si_key si = si_key si' by rewrite /si_key e.
    by rewrite (session_of_key_inj (rl := Resp) ss ss' ek).
- iIntros "#rel".
  rewrite /si_key public_senc_key.
  iApply (public_THashIS with "Hpred [] []").
  + by iEval (rewrite /si_key minted_senc minted_hash_result) in "m_k".
  + iNext; iModIntro; iExists si.
    by do !iSplit => //.
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
