From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import reservation_map.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib.
From cryptis.lib Require Import gmeta nown saved_prop.
From cryptis Require Import cryptis primitives tactics role.
From cryptis.lib Require Import dh.
From cryptis.examples.iso_dh Require Import impl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Record sess_info := SessInfo {
  si_init : sign_key;
  si_resp : sign_key;
  si_init_share : term;
  si_resp_share : term;
  si_secret : term;
}.

Definition si_share_of rl :=
  if rl is Init then si_init_share
  else si_resp_share.

#[global] Instance sess_info_inhabited : Inhabited sess_info :=
  populate (SessInfo inhabitant inhabitant
              inhabitant inhabitant inhabitant).

Class iso_dhGpreS Σ := IsoDhGPreS {
  #[local] iso_dhGpreS_meta :: metaGS Σ;
  #[local] iso_dhGpreS_pred :: savedPredG Σ (sess_info * option role);
}.

Class iso_dhGS Σ := IsoDhGS {
  #[local] iso_dh_inG :: iso_dhGpreS Σ;
  iso_dh_name : gname;
}.

Definition iso_dhΣ := #[
  metaΣ;
  savedPredΣ (sess_info * option role)
].

#[global] Instance subG_iso_dhGpreS Σ : subG iso_dhΣ Σ → iso_dhGpreS Σ.
Proof. solve_inG. Qed.

Section Verif.

Context `{!heapGS Σ, !cryptisGS Σ, !iso_dhGS Σ}.
Abbreviation iProp := (iProp Σ).

Implicit Types (rl : role) (t nI nR sI sR kS : term).
Implicit Types (skI skR : sign_key).
Implicit Types (si : sess_info).
Implicit Types (N : namespace) (E : coPset).
Implicit Types (φ : sess_info → role → iProp) (ρ : sess_info → iProp).

Definition iso_dh_token E : iProp :=
  gmeta_token iso_dh_name E.

(* One saved predicate holds a usage's gifts, at [Some rl], and its release
   condition, at [None]. *)
Definition iso_dh_pred N φ ρ : iProp :=
  nown iso_dh_name N
    (saved_pred DfracDiscarded (λ '(si, o),
       if o is Some rl then φ si rl else ρ si)).

Lemma iso_dh_pred_set N φ ρ E :
  ↑N ⊆ E →
  iso_dh_token E ==∗ iso_dh_pred N φ ρ ∗ iso_dh_token (E ∖ ↑N).
Proof. by iIntros "%"; iApply nown_alloc. Qed.

Lemma iso_dh_token_difference E1 E2 :
  E1 ⊆ E2 →
  iso_dh_token E2 ⊣⊢ iso_dh_token E1 ∗ iso_dh_token (E2 ∖ E1).
Proof. exact: gmeta_token_difference. Qed.

Lemma iso_dh_token_drop E1 E2 :
  E1 ⊆ E2 →
  iso_dh_token E2 -∗ iso_dh_token E1.
Proof. exact: gmeta_token_drop. Qed.

Lemma iso_dh_pred_agree N φ ρ φ' ρ' :
  iso_dh_pred N φ ρ -∗
  iso_dh_pred N φ' ρ' -∗
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
Definition iso_dh_ready N si rl : iProp := ∀ φ ρ,
  iso_dh_pred N φ ρ →
  term_token (si_share_of rl si) (↑iso_dhN.@"ready") ={⊤}=∗
    ▷ φ si rl.

Lemma iso_dh_ready_alloc N si rl φ ρ :
  iso_dh_pred N φ ρ -∗
  φ si rl ={⊤}=∗
  □ iso_dh_ready N si rl.
Proof.
iIntros "#N_φ φ_ts".
iMod (escrowI nroot with "φ_ts []") as "#?".
{ by iApply (term_token_switch (si_share_of rl si) (iso_dhN.@"ready")). }
iIntros "!> !>  %φ' %ρ' #N_φ' ready".
iDestruct (iso_dh_pred_agree with "N_φ N_φ'") as "[#φ_eq _]".
iSpecialize ("φ_eq" $! si rl).
iMod (escrowE with "[//] ready") as "res" => //.
iIntros "!> !>". by iRewrite -"φ_eq".
Qed.

Lemma wp_mk_keyshare (t : term) :
  {{{ True }}}
    mk_keyshare t
  {{{ RET (repr (TExp (TInt 0) t)); True : iProp}}}.
Proof.
iIntros "%Φ _ Hpost". wp_lam.
wp_bind (tint _). iApply wp_tint.
wp_bind (texp _ _). iApply wp_texp.
by iApply "Hpost".
Qed.

Definition si_key si : senc_key :=
  SEncKey
    (Spec.of_list [Spec.pkey (si_init si);
                   Spec.pkey (si_resp si);
                   si_init_share si;
                   si_resp_share si;
                   si_secret si]).
Arguments si_key : simpl never.

Lemma session_agree si1 si2 :
  si_key si1 = si_key si2 →
  si1 = si2.
Proof.
case: si1 si2
  => [[skI1] [skR1] ga1 gb1 gab1] [[skI2] [skR2] ga2 gb2 gab2] /=.
rewrite /si_key /=. case => /Spec.of_list_inj.
by case=> /Spec.sign_pkey_inj <- /Spec.sign_pkey_inj <- <- <- <-.
Qed.

(** The responder records the usage of a session on its share, which ties the
    initiator's last message to it. *)
Definition usage gb N : iProp :=
  term_meta gb (iso_dhN.@"usage") N.

(** When [rl] completed [si], it could not rule out a forged signature. *)
Definition compromised rl si : iProp :=
  term_meta (si_share_of rl si) (iso_dhN.@"compromised") true.

#[global] Instance compromised_persistent rl si :
  Persistent (compromised rl si).
Proof. apply _. Qed.

#[global] Instance compromised_timeless rl si :
  Timeless (compromised rl si).
Proof. apply _. Qed.

(** A compromised session has a leaked long-term key, and the initiator then
    also makes the key public.  The responder cannot: it cannot tell a forged
    last message from a genuine one, and publishing its share would break the
    initiator's forward secrecy. *)
Definition session ρ rl si : iProp :=
  minted (si_key si) ∗
  □ (▷ □ ρ si → public (si_key si)) ∗
  (compromised rl si ∗ (public (si_init si) ∨ public (si_resp si)) ∗
     (if rl is Init then public (si_key si) else True) ∨
   □ (¬ compromised rl si) ∗ □ (public (si_key si) → ▷ □ ρ si)).

#[global] Instance session_persistent ρ rl si : Persistent (session ρ rl si).
Proof. by case: rl; apply _. Qed.

Lemma session_minted ρ rl si : session ρ rl si -∗ minted (si_key si).
Proof. by iIntros "[? _]". Qed.

Lemma session_release ρ rl si :
  session ρ rl si -∗ □ (▷ □ ρ si → public (si_key si)).
Proof. by iIntros "(_ & ? & _)". Qed.

Lemma session_ok ρ rl si :
  session ρ rl si -∗
  ¬ compromised rl si -∗
  □ (public (si_key si) ↔ ▷ □ ρ si).
Proof.
iIntros "(_ & #rel & [(#c & _)|(_ & #ok)]) nc".
- by iDestruct ("nc" with "c") as "[]".
- iModIntro. by iSplit.
Qed.

Lemma session_compromised ρ rl si :
  session ρ rl si -∗
  compromised rl si -∗
  (public (si_init si) ∨ public (si_resp si)) ∗
  (if rl is Init then public (si_key si) else True).
Proof.
iIntros "(_ & _ & [(_ & #l & #p)|(#nc & _)]) #c"; first by iSplit.
by iDestruct ("nc" with "c") as "[]".
Qed.

Lemma secret_session ρ rl si :
  secret (si_init si) -∗
  secret (si_resp si) -∗
  session ρ rl si -∗
  ◇ □ (¬ compromised rl si).
Proof.
iIntros "sI sR (_ & _ & [(_ & [#l|#l] & _)|(#nc & _)])";
  last by iIntros "!> !>".
- by iDestruct (secret_not_public with "sI l") as ">[]".
- by iDestruct (secret_not_public with "sR l") as ">[]".
Qed.

Definition msg2_pred skR m2 : iProp :=
  ∃ ga (b : nonce) skI N φ ρ,
    let gb := TExp (TInt 0) b in
    let si := SessInfo skI skR ga gb (TExp ga b) in
    ⌜m2 = Spec.of_list [ga; gb; Spec.pkey skI; Tag N]⌝ ∧
    iso_dh_pred N φ ρ ∧
    □ (public b ↔ ▷ □ ρ si) ∧
    (∀ t, exp_pred b t ↔ ▷ □ dh_key_share t) ∧
    usage gb N ∧
    iso_dh_ready N si Init.

Definition msg3_pred skI m3 : iProp :=
  ∃ (a : nonce) gb skR,
    let ga := TExp (TInt 0) a in
    let si := SessInfo skI skR ga gb (TExp gb a) in
    ⌜m3 = Spec.of_list [ga; gb; Spec.pkey skR]⌝ ∧
    ((public skI ∨ public skR) ∨
     ∃ N φ ρ, usage gb N ∧ iso_dh_pred N φ ρ ∧
       □ (public (si_key si) → ▷ □ ρ si) ∧ iso_dh_ready N si Resp).

Definition iso_dh_ctx : iProp :=
  sign_pred (iso_dhN.@"m2") msg2_pred ∗
  sign_pred (iso_dhN.@"m3") msg3_pred.

Lemma iso_dh_ctx_alloc E :
  ↑iso_dhN ⊆ E →
  seal_pred_token SIGN E ==∗
  iso_dh_ctx ∗ seal_pred_token SIGN (E ∖ ↑iso_dhN).
Proof.
iIntros "%sub token".
iMod (sign_pred_set (N := iso_dhN.@"m2") msg2_pred with "token")
  as "[? token]"; try solve_ndisj. iFrame.
iMod (sign_pred_set (N := iso_dhN.@"m3") msg3_pred with "token")
  as "[? token]"; try solve_ndisj. iFrame.
iApply (seal_pred_token_drop with "token"). solve_ndisj.
Qed.

End Verif.

Arguments iso_dh_ctx_alloc {Σ _ _ _} E.

Lemma iso_dhGS_alloc `{!heapGS Σ, !cryptisGS Σ} E :
  ↑iso_dhN ⊆ E →
  iso_dhGpreS Σ →
  seal_pred_token SIGN E ={⊤}=∗ ∃ (H : iso_dhGS Σ),
    iso_dh_ctx ∗ iso_dh_token ⊤ ∗
    seal_pred_token SIGN (E ∖ ↑iso_dhN).
Proof.
iIntros "% %Hpre token".
iMod gmeta_token_alloc as (γ_meta) "own".
set iso_dhGS0 := {| iso_dh_inG := Hpre; iso_dh_name := γ_meta |} : iso_dhGS Σ.
iExists iso_dhGS0.
iMod (iso_dh_ctx_alloc with "token") as "[#H ?]" => //.
by iFrame.
Qed.

Arguments iso_dhGS_alloc {Σ _ _ E}.
Arguments iso_dh_pred_set {Σ _} N φ ρ E.
