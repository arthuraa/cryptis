From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import par.
From iris.algebra Require Import auth gset.
From cryptis Require Import lib term cryptis primitives tactics role.
From cryptis.lib Require Import dh hmqv gmeta nown saved_prop.

From cryptis.examples Require Import alist iso_dh.
From cryptis.examples.opaque Require Import impl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * OPAQUE: shared definitions

    This file provides several basic OPAQUE definitions, including:

    - The session record containing all the data that the parties agree on; and

    - The hash/encryption predicates used by the protocol.

    The HMQV key-exchange formula and its algebra come from
    [cryptis/lib/hmqv.v].

    We state authentication as for [examples/hmqv]: each party can send to its
    peer resources that pertain to the newly established session, and the
    usage of the protocol fixes when the key of a session is released.  The
    password may become public, and so may the server's file; the client's
    long-term key is as secret as the password, and the ephemeral private keys
    are deleted right away.  A party that could not rule out a forged
    authenticator marks its session compromised; otherwise the key of the
    session is public exactly when released. *)

Definition hash_result (tag : string) (val : term) : term :=
  THash (Spec.tag (Tag $ opN.@tag) val).

Lemma hash_result_inj (tag1 tag2 : string) t1 t2 :
  hash_result tag1 t1 = hash_result tag2 t2 -> tag1 = tag2 /\ t1 = t2.
Proof.
rewrite /hash_result => - [] /Spec.tag_inj [] /Tag_inj c ->.
by case: (ndot_inj _ _ _ _ c).
Qed.

Lemma TExp_g_inj (p p' : nonce) : TExp g p = TExp g p' -> p = p'.
Proof.
move=> e; suff : p = p' :> term by case.
exact: (TExp_injr (Ngmul_neq_unit (t := g) I)).
Qed.

(** * Session information

    This record contains all the information that is relevant to an OPAQUE
    session. *)

Record sess_info := SessInfo {
  si_uid    : term;   (* client identity, public *)
  si_ckey   : term;   (* P_u = g^p_u, the client's long-term public key *)
  si_skey   : term;   (* P_s = g^p_s, the server's long-term public key *)
  si_blind  : term;   (* α = (H' pw)^r, the client's per-session share *)
  si_cshare : term;   (* X_u = g^x_u *)
  si_sshare : term;   (* X_s = g^x_s *)
  si_secret : term;   (* the HMQV group element *)
}.

Definition si_ssid si :=
  hash_result "H" (Spec.of_list [si_uid si; si_blind si]).
Definition si_K si := hash_result "H" (Spec.of_list [si_secret si]).
Definition si_key si := hash_result "SK" (Spec.of_list [si_K si; si_ssid si]).
Definition si_result si := Spec.of_list [si_uid si; si_key si].

(** Build a [sess_info] record based on the values accessible by the server. *)
Definition server_si (uid α X_u P_u p_s x_s : term) : sess_info :=
  SessInfo uid P_u (TExp g p_s) α X_u (TExp g x_s)
    (hmqv_K opN "e" "d" p_s x_s (TExp g p_s) (TExp g x_s) P_u X_u).

(** The record the client builds on its own when it cannot trust the server's,
    i.e. when the password was already public. *)
Definition client_si (uid P_u P_s α x_u X_s p_u : term) : sess_info :=
  SessInfo uid P_u P_s α (TExp g x_u) X_s
    (hmqv_K opN "d" "e" p_u x_u P_u (TExp g x_u) P_s X_s).

(** The client mints a token on its blind [α]: the server keys the resource
    escrow on the [↑opN.@"ready"] slice and the client returns the rest to its
    caller.  The server's own token is on its share [X_s], as in [iso_dh]. *)

Definition client_fresh_set (pw : term) (t : nonce) : gset term :=
  {[TExp (hash_result "H" pw) t]}.

(** The server's view of a session is determined by its key: this is what the
    game needs to tell two server sessions apart, and what each party needs to
    read the peer's data off the peer's authenticator. *)
Lemma server_si_key_inj uid α X_u (p_u p_s x_s : nonce)
                        uid' α' X_u' (p_u' p_s' x_s' : nonce) :
  si_key (server_si uid α X_u (TExp g p_u) p_s x_s)
  = si_key (server_si uid' α' X_u' (TExp g p_u') p_s' x_s') ->
  server_si uid α X_u (TExp g p_u) p_s x_s
  = server_si uid' α' X_u' (TExp g p_u') p_s' x_s'.
Proof.
rewrite /si_key /si_K /si_ssid /server_si /=.
move/hash_result_inj => - [] _ /Spec.of_list_inj [] eK essid.
move/Spec.tag_inj: eK => - [] _ /Spec.of_list_inj [] eK.
move/Spec.tag_inj: essid => - [] _ /Spec.of_list_inj [] -> ->.
have nP (p : nonce) : TExp g p ≠ TGMul ∅.
  exact: Ngmul_neq_unit (Ngmul_TExp g _ I).
have: p_s = p_s' ∧ x_s = x_s' ∧ TExp g p_u = TExp g p_u' ∧ X_u = X_u'.
  apply: (hmqv_K_inj (g := g) I I _ (nP _) (nP _)
            (hmqv_K_neq_unit (g := g) I I) eK) => //.
case=> -> [] -> [] /TExp_g_inj -> ->; congruence.
Qed.

Definition server_session si : Prop :=
  ∃ uid α X_u (p_u p_s x_s : nonce),
    si = server_si uid α X_u (TExp g p_u) p_s x_s.

Lemma server_session_key_inj si1 si2 :
  server_session si1 -> server_session si2 ->
  si_key si1 = si_key si2 -> si1 = si2.
Proof.
move=> [uid [α [X_u [p_u [p_s [x_s ->]]]]]].
move=> [uid' [α' [X_u' [p_u' [p_s' [x_s' ->]]]]]].
exact: server_si_key_inj.
Qed.

Lemma si_key_blind_inj si1 si2 :
  si_key si1 = si_key si2 -> si_blind si1 = si_blind si2.
Proof.
rewrite /si_key /si_ssid.
move/hash_result_inj => - [] _ e; apply Spec.of_list_inj in e.
move/(f_equal (λ l, nth 1 l (TInt 0))): e => /= e.
move/hash_result_inj: e => - [] _ e; apply Spec.of_list_inj in e.
by move/(f_equal (λ l, nth 1 l (TInt 0))): e => /=.
Qed.

(** The term each role holds a token on, and what the game must know about a
    session to read its share off its key. *)
Definition share_of (rl : role) si : term :=
  if rl is Init then si_blind si else si_sshare si.

Definition session_of (rl : role) si : Prop :=
  if rl is Resp then server_session si else True.

Lemma share_of_key_inj rl si1 si2 :
  session_of rl si1 -> session_of rl si2 ->
  si_key si1 = si_key si2 -> share_of rl si1 = share_of rl si2.
Proof.
case: rl => /= [_ _|ss1 ss2]; first exact: si_key_blind_inj.
by move=> e; rewrite (server_session_key_inj ss1 ss2 e).
Qed.

Class opaqueGpreS Σ := OpaqueGPreS {
  #[local] opaqueGpreS_meta :: metaGS Σ;
  #[local] opaqueGpreS_pred :: savedPredG Σ (sess_info * role);
  #[local] opaqueGpreS_log :: inG Σ (authR (gsetUR term));
}.

Class opaqueGS Σ := OpaqueGS {
  #[local] opaque_inG :: opaqueGpreS Σ;
  opaque_name : gname;
}.

Definition opaqueΣ := #[
  metaΣ;
  savedPredΣ (sess_info * role);
  GFunctor (authR (gsetUR term))
].

#[global] Instance subG_opaqueGpreS Σ : subG opaqueΣ Σ → opaqueGpreS Σ.
Proof. solve_inG. Qed.

Section Opaque.

Context `{!cryptisGS Σ, !heapGS Σ, !spawnG Σ, !opaqueGS Σ}.
Abbreviation iProp := (iProp Σ).

Abbreviation opN := (nroot.@"op").

Implicit Types (si : sess_info) (φ : sess_info → role → iProp).
Implicit Types (ρ : sess_info → iProp).

(** The hash of the session key: released sessions publish their key through
    it. *)
Definition SK_pred ρ (t : term) : iProp :=
  ∃ si, ⌜t = Spec.of_list [si_K si; si_ssid si]⌝ ∗
        ⌜server_session si⌝ ∗
        □ ρ si.

(** OPAQUE has a single usage: [φ si rl] is what the party with role [rl]
    receives from its peer in [si], and [ρ si] releases the key of [si]. *)
Definition opaque_token : iProp :=
  gmeta_token opaque_name (↑opN.@"res") ∗ hash_pred_token (↑opN.@"SK").

Definition opaque_pred φ ρ : iProp :=
  nown opaque_name (opN.@"res")
    (saved_pred DfracDiscarded (λ '(si, rl), φ si rl)) ∗
  hash_pred (opN.@"SK") (SK_pred ρ).

Lemma opaque_pred_set φ ρ : opaque_token ==∗ opaque_pred φ ρ.
Proof.
iIntros "[tok tok_SK]".
iMod (hash_pred_set (opN.@"SK") (SK_pred ρ) with "tok_SK") as "[$ _]";
  first done.
by iMod (nown_alloc with "tok") as "[$ _]".
Qed.

(** The resource a party escrows for its peer, redeemable once with the
    [ready] slice of the token on the peer's share. *)
Definition opaque_ready si rl : iProp :=
  ∀ φ ρ, opaque_pred φ ρ →
  term_token (share_of rl si) (↑opN.@"ready") ={⊤}=∗ ▷ φ si rl.

Lemma opaque_ready_alloc si rl φ ρ :
  opaque_pred φ ρ -∗
  φ si rl ={⊤}=∗
  □ opaque_ready si rl.
Proof.
iIntros "#[N_φ _] φ_si".
iMod (escrowI nroot with "φ_si []") as "#?".
{ by iApply (term_token_switch (share_of rl si) (opN.@"ready")). }
iIntros "!> !> %φ' %ρ' #[N_φ' _] ready".
iPoseProof (nown_valid_2 with "N_φ N_φ'") as "#valid".
iPoseProof (saved_pred_op_validI with "valid") as "[_ #φ_eq]".
iSpecialize ("φ_eq" $! (si, rl)).
iMod (escrowE with "[//] ready") as "res" => //.
iIntros "!> !>". by iRewrite -"φ_eq".
Qed.

(** The identity equations the specifications export, in the style of
    [iso_dh]'s [session skI skR si]: indexed by the client's identity only,
    since that is all the client supplies -- it *learns* the server's, which is
    then [si_skey si]. *)
Definition opaque_session_for uid si : iProp :=
  ⌜si_uid si = uid⌝ ∗ public (si_uid si) ∗ minted (si_key si) ∗
  public (si_ckey si) ∗ public (si_skey si).

(** * The password file

    The server's file for [pw] holds the server's long-term key and the OPRF
    key, which are as secret as the file.  The OPRF key consents only to the
    bases of the points the server evaluated, which it logs on [pw]. *)

Definition stolen pw : iProp := term_meta pw (opN.@"stolen") true.

#[global] Instance stolen_persistent pw : Persistent (stolen pw).
Proof. apply _. Qed.

#[global] Instance stolen_timeless pw : Timeless (stolen pw).
Proof. apply _. Qed.

(** Whoever holds this token decides when the file is stolen. *)
Definition file_secret pw : iProp := term_token pw (↑opN.@"stolen").

Lemma file_secret_stolen pw : file_secret pw -∗ stolen pw -∗ False.
Proof. exact: term_meta_token. Qed.

Lemma steal_file pw : file_secret pw ==∗ stolen pw.
Proof. exact: term_meta_set. Qed.

Definition oprf_log pw (B : gset term) : iProp :=
  term_own pw (opN.@"log") (● B) ∗ [∗ set] b ∈ B, minted b.

Definition oprf_queried pw b : iProp :=
  term_own pw (opN.@"log") (◯ ({[b]} : gset term)).

#[global] Instance oprf_queried_persistent pw b :
  Persistent (oprf_queried pw b).
Proof. apply _. Qed.

Definition oprf_pred pw t : iProp := ∃ b, oprf_queried pw b ∗ ⌜base t = b⌝.

Lemma oprf_log_alloc pw : term_token pw (↑opN.@"log") ==∗ oprf_log pw ∅.
Proof.
iIntros "tok".
iMod (term_own_alloc (opN.@"log") (● (∅ : gset term)) with "tok")
  as "[$ _]" => //.
- by apply auth_auth_valid.
- by rewrite big_sepS_empty.
Qed.

Lemma oprf_log_queried pw B b :
  oprf_log pw B -∗ oprf_queried pw b -∗ ⌜b ∈ B⌝.
Proof.
iIntros "[auth _] frag".
iDestruct (term_own_valid_2 with "auth frag")
  as %[sub _]%auth_both_valid_discrete.
iPureIntro. move: sub. rewrite gset_included. set_solver.
Qed.

Lemma oprf_log_query pw B B' :
  ([∗ set] b ∈ B', minted b) -∗
  oprf_log pw B ==∗
  oprf_log pw (B' ∪ B) ∗ [∗ set] b ∈ B', oprf_queried pw b.
Proof.
iIntros "#m_B' [auth #m_B]".
iMod (term_own_update (● (B' ∪ B) ⋅ ◯ B') with "auth") as "auth".
{ apply: auth_update_alloc.
  rewrite -{2}(union_empty_r_L B') -!gset_op.
  by apply: op_local_update_discrete. }
iDestruct (term_own_op with "auth") as "[auth #frag]".
iModIntro. iSplitL "auth".
- iFrame. rewrite big_sepS_union_pers. by iSplit.
- iApply big_sepS_intro. iIntros "!> %b %b_B'".
  iApply (term_own_mono with "frag").
  apply: auth_frag_mono. rewrite gset_included. set_solver.
Qed.

(** Before the file is stolen, the attacker knows the OPRF at a point only if
    the server evaluated it at that point. *)
Lemma public_oprf pw (k_s : nonce) t :
  negb (is_exp t) → negb (is_gmul t) →
  □ (public k_s ↔ ▷ □ stolen pw) -∗
  □ (∀ t', exp_pred k_s t' ↔ ▷ □ oprf_pred pw t') -∗
  public (TExp t k_s) -∗
  ▷ (stolen pw ∨ oprf_queried pw t).
Proof.
move=> Nx Nm; iIntros "#s_k #e_k #p".
iEval (rewrite public_TExp_iff //) in "p".
iDestruct "p" as "(_ & _ & [p|p] & _)".
- iDestruct ("s_k" with "p") as "#s". iNext. by iLeft.
- iDestruct ("e_k" with "p") as "#q". iNext.
  iDestruct "q" as "(%b & q & %e)". iRight.
  by rewrite base_TExp // base_expN // in e; subst b.
Qed.

(** * Compromise

    Whoever stole the file can impersonate the server, but not the client. *)

(** When [rl] completed [si], it could not rule out a forged authenticator. *)
Definition compromised (rl : role) si : iProp :=
  term_meta (share_of rl si) (opN.@"compromised") true.

#[global] Instance compromised_persistent rl si :
  Persistent (compromised rl si).
Proof. apply _. Qed.

#[global] Instance compromised_timeless rl si :
  Timeless (compromised rl si).
Proof. apply _. Qed.

Definition session pw ρ (rl : role) si : iProp :=
  minted (si_key si) ∗
  □ (▷ □ ρ si → public (si_key si)) ∗
  (compromised rl si ∗ public (si_key si) ∗
     (public pw ∨ ⌜rl = Init⌝ ∗ stolen pw) ∨
   □ (¬ compromised rl si) ∗ □ (public (si_key si) → ▷ □ ρ si)).

#[global] Instance session_persistent pw ρ rl si :
  Persistent (session pw ρ rl si).
Proof. apply _. Qed.

Lemma session_minted pw ρ rl si : session pw ρ rl si -∗ minted (si_key si).
Proof. by iIntros "[? _]". Qed.

Lemma session_release pw ρ rl si :
  session pw ρ rl si -∗ □ (▷ □ ρ si → public (si_key si)).
Proof. by iIntros "(_ & ? & _)". Qed.

Lemma session_ok pw ρ rl si :
  session pw ρ rl si -∗
  ¬ compromised rl si -∗
  □ (public (si_key si) ↔ ▷ □ ρ si).
Proof.
iIntros "(_ & #rel & [(#c & _)|(_ & #ok)]) nc".
- by iDestruct ("nc" with "c") as "[]".
- iModIntro. by iSplit.
Qed.

Lemma session_compromised pw ρ rl si :
  session pw ρ rl si -∗
  compromised rl si -∗
  public (si_key si) ∗ (public pw ∨ ⌜rl = Init⌝ ∗ stolen pw).
Proof.
iIntros "(_ & _ & [(_ & #p & #pw)|(#nc & _)]) #c"; first by iSplit.
by iDestruct ("nc" with "c") as "[]".
Qed.

Lemma secret_session pw ρ rl si :
  secret pw -∗
  (if rl is Init then file_secret pw else True) -∗
  session pw ρ rl si -∗
  ◇ □ (¬ compromised rl si).
Proof.
iIntros "s_pw s_file (_ & _ & [(_ & _ & [#p_pw|[-> #st]])|(#nc & _)])".
- by iDestruct (secret_not_public with "s_pw p_pw") as ">[]".
- by iDestruct (file_secret_stolen with "s_file st") as "[]".
- by iIntros "!> !>".
Qed.

Lemma _wp_H (tag : string) (val : term) Ψ:
  Ψ (repr (hash_result tag val)) ⊢ WP _H tag val {{ Ψ }}.
Proof.
iIntros "post".
wp_lam.
wp_apply wp_tag.
wp_apply wp_hash.
by iApply "post".
Qed.

Lemma _wp_H_list (tag : string) (val : list term) Ψ:
  Ψ (repr (hash_result tag (Spec.of_list val))) ⊢
  WP _H_list tag (repr val) {{ Ψ }}.
Proof.
iIntros "post".
wp_lam.
wp_apply wp_term_of_list.
by wp_apply _wp_H.
Qed.

Definition wp_prf   := _wp_H_list.
Definition wp_H     := _wp_H_list.
Definition wp_H'    := _wp_H.

Lemma minted_hash_result tag t : minted (hash_result tag t) ⊣⊢ minted t.
Proof. by rewrite /hash_result minted_THash minted_tag. Qed.

Lemma client_fresh_set_minted pw :
  minted pw -∗
  ∀ r : nonce, [∗ set] t' ∈ client_fresh_set pw r, □ (minted r ↔ minted t').
Proof.
iIntros "#m_pw %r".
rewrite /client_fresh_set.
rewrite big_sepS_singleton.
iModIntro; iSplit.
- iIntros "#?"; iApply all_minted_TExp; iSplit => //.
  by rewrite minted_hash_result.
- rewrite (minted_TExp (t1 := hash_result "H" pw) (TNonce r) I I).
  by iIntros "[_ ?]".
Qed.

(** The long-term keys registered with [pw]: the client's is as secret as the
    password, and the server's as the file. *)
Definition opaque_keys pw (p_u p_s : nonce) : iProp :=
  hmqv_key p_u ∗ hmqv_key p_s ∗
  □ (public p_u ↔ ▷ □ public pw) ∗ □ (public p_s ↔ ▷ □ stolen pw).

#[global] Instance opaque_keys_persistent pw p_u p_s :
  Persistent (opaque_keys pw p_u p_s).
Proof. apply _. Qed.

(** The client's authenticator vouches for its ephemeral and escrows the
    server's resources. *)
Definition A_u_pred (t : term) : iProp :=
  ∃ si (x_u : nonce),
    ⌜t = Spec.of_list [si_K si; si_ssid si]⌝ ∗
    ⌜server_session si⌝ ∗
    ⌜si_cshare si = TExp g x_u⌝ ∗
    ephemeral x_u ∗
    opaque_ready si Resp.

(** The server's does the same for the client. *)
Definition A_s_pred (t : term) : iProp :=
  ∃ uid α X_u (p_u p_s x_s : nonce),
    let si := server_si uid α X_u (TExp g p_u) p_s x_s in
    ⌜t = Spec.of_list [si_K si; si_ssid si]⌝ ∗
    ephemeral x_s ∗
    public (si_ckey si) ∗ public (si_skey si) ∗
    opaque_ready si Init.


(* The key pins the password: the client compares it with its own. *)
Definition envelope_pred (sk : senc_key) (t : term) : iProp :=
  ∃ pw β (p_u p_s : nonce),
      ⌜sk = SEncKey (hash_result "H" (Spec.of_list [pw; β]))⌝ ∗
      ⌜t = Spec.of_list [TNonce p_u; TExp g p_u; TExp g p_s]⌝ ∗
      opaque_keys pw p_u p_s.

Definition opaque_ctx : iProp :=
  hash_pred (opN.@"H") (λ _ : term, False%I) ∗
  hash_pred (opN.@"A_s") A_s_pred ∗
  hash_pred (opN.@"A_u") A_u_pred ∗
  senc_pred (opN.@"AuthEnc") envelope_pred.

Lemma opaque_alloc E :
  ↑opN ⊆ E →
  hash_pred_token E -∗
  seal_pred_token SENC E ==∗
  opaque_ctx ∗
  hash_pred_token (↑opN.@"SK") ∗
  hash_pred_token (E ∖ ↑opN) ∗
  seal_pred_token SENC (E ∖ ↑opN).
Proof.
iIntros "%sub h_token s_token".
rewrite (hash_pred_token_difference (↑opN) E) //.
iDestruct "h_token" as "[h_token $]".
iMod (hash_pred_set (opN.@"H") (λ _ : term, False%I) with "h_token")
  as "[? h_token]"; try solve_ndisj; iFrame.
iMod (hash_pred_set (opN.@"A_s") A_s_pred with "h_token")
  as "[? h_token]"; try solve_ndisj; iFrame.
iMod (hash_pred_set (opN.@"A_u") A_u_pred with "h_token")
  as "[? h_token]"; try solve_ndisj; iFrame.
iMod (senc_pred_set (N := opN.@"AuthEnc") envelope_pred with "s_token")
  as "[? s_token]"; try solve_ndisj; iFrame.
iSplitL "h_token".
- iApply (hash_pred_token_drop with "h_token"). solve_ndisj.
- iApply (seal_pred_token_drop with "s_token"). solve_ndisj.
Qed.

Lemma hmqv_key_public (p : nonce) : hmqv_key p -∗ public (TExp g p).
Proof.
iIntros "[#m_p #pred_p]"; iApply public_dh_share => //; by rewrite public_TInt.
Qed.

(** Both roles conclude the same way once they know the peer's share is an
    honest ephemeral: only release can publish the key. *)
Lemma honest_session uid α (p_u p_s x_u x_s : nonce) φ ρ :
  let si := server_si uid α (TExp g x_u) (TExp g p_u) p_s x_s in
  opaque_pred φ ρ -∗
  hash_pred (opN.@"H") (λ _ : term, False%I) -∗
  public uid -∗
  public α -∗
  hmqv_key p_u -∗
  hmqv_key p_s -∗
  ephemeral x_u -∗
  ephemeral x_s -∗
  minted (si_key si) -∗
  □ (public (si_key si) ↔ ▷ □ ρ si).
Proof.
move=> si.
iIntros "#[_ HpredSK] #HpredH #p_uid #p_α #key_pu #key_ps #[key_xu s_xu]
         #[key_xs s_xs] #m_SK".
have ss : server_session si by exists uid, α, (TExp g x_u), p_u, p_s, x_s.
iModIntro; iSplit.
- iIntros "#p_SK".
  iDestruct (public_THashE with "HpredSK p_SK") as "[p_t | [_ #rel]]".
  + rewrite public_of_list /=.
    iDestruct "p_t" as "[p_K _]".
    iDestruct (public_THashE with "HpredH p_K") as "[p_t | [_ contra]]";
      last by iNext; iDestruct "contra" as "[]".
    rewrite public_of_list /=.
    iDestruct "p_t" as "[p_K' _]".
    iAssert (public p_s ∗ public x_s ∨ public p_u ∗ public x_u)%I
      as "#[[_ #p]|[_ #p]]".
    { by iApply (public_hmqv_K_honest
                   with "key_ps key_xs key_pu key_xu p_K'") => //. }
    * iDestruct ("s_xs" with "p") as "f". iNext. by iDestruct "f" as "[]".
    * iDestruct ("s_xu" with "p") as "f". iNext. by iDestruct "f" as "[]".
  + iNext. iDestruct "rel" as "(%si' & %e & %ss' & #rel')".
    have ek : si_key si = si_key si' by rewrite /si_key e.
    by rewrite (server_session_key_inj ss ss' ek).
- iIntros "#rel".
  iApply (public_THashIS with "HpredSK [] []").
  + by iEval (rewrite /si_key minted_hash_result) in "m_SK".
  + iNext; iModIntro; iExists si. by do !iSplit => //.
Qed.
End Opaque.

Lemma opaqueGS_alloc `{!heapGS Σ, !cryptisGS Σ} E :
  ↑opN ⊆ E →
  opaqueGpreS Σ →
  hash_pred_token E -∗
  seal_pred_token SENC E ={⊤}=∗ ∃ (H : opaqueGS Σ),
    opaque_ctx ∗ opaque_token ∗
    hash_pred_token (E ∖ ↑opN) ∗
    seal_pred_token SENC (E ∖ ↑opN).
Proof.
iIntros "% %Hpre h_token s_token".
iMod gmeta_token_alloc as (γ_meta) "own".
set opaqueGS0 := {| opaque_inG := Hpre; opaque_name := γ_meta |} : opaqueGS Σ.
iExists opaqueGS0.
iMod (opaque_alloc with "h_token s_token") as "($ & $ & $ & $)" => //.
iModIntro. iApply (gmeta_token_drop with "own"). set_solver.
Qed.
