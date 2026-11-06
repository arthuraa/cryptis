From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import reservation_map.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib.
From cryptis.lib Require Import gmeta nown saved_prop.
From cryptis Require Import cryptis primitives tactics role.
From cryptis.examples.nsl_dh Require Import impl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Record sess_info := SessInfo {
  si_init : aenc_key;
  si_resp : aenc_key;
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

Class nsl_dhGpreS Σ := NslDhGPreS {
  #[local] nsl_dhGpreS_meta :: metaGS Σ;
  #[local] nsl_dhGpreS_pred :: savedPredG Σ (sess_info * option role);

}.

Class nsl_dhGS Σ := NslDhGS {
  #[local] nsl_dh_inG :: nsl_dhGpreS Σ;
  nsl_dh_name : gname;
}.

Definition nsl_dhΣ := #[
  metaΣ;
  savedPredΣ (sess_info * option role)

].

#[global] Instance subG_nsl_dhGpreS Σ : subG nsl_dhΣ Σ → nsl_dhGpreS Σ.
Proof. solve_inG. Qed.

Section Verif.

Context `{!heapGS Σ, !cryptisGS Σ, !nsl_dhGS Σ}.
Abbreviation iProp := (iProp Σ).

Implicit Types (rl : role) (t ga gb : term).
Implicit Types (skI skR : aenc_key).
Implicit Types (si : sess_info).
Implicit Types (N : namespace) (E : coPset).
Implicit Types (φ : sess_info → role → iProp) (ρ : sess_info → iProp).

Definition nsl_dh_token E : iProp :=
  gmeta_token nsl_dh_name E.

(* One saved predicate holds a usage's gifts, at [Some rl], and its release
   condition, at [None]. *)
Definition nsl_dh_pred N φ ρ : iProp :=
  nown nsl_dh_name N
    (saved_pred DfracDiscarded (λ '(si, o),
       if o is Some rl then φ si rl else ρ si)).

Lemma nsl_dh_pred_set N φ ρ E :
  ↑N ⊆ E →
  nsl_dh_token E ==∗ nsl_dh_pred N φ ρ ∗ nsl_dh_token (E ∖ ↑N).
Proof. by iIntros "%"; iApply nown_alloc. Qed.

Lemma nsl_dh_token_difference E1 E2 :
  E1 ⊆ E2 →
  nsl_dh_token E2 ⊣⊢ nsl_dh_token E1 ∗ nsl_dh_token (E2 ∖ E1).
Proof. exact: gmeta_token_difference. Qed.

Lemma nsl_dh_token_drop E1 E2 :
  E1 ⊆ E2 →
  nsl_dh_token E2 -∗ nsl_dh_token E1.
Proof. exact: gmeta_token_drop. Qed.

#[local] Lemma nsl_dh_pred_agree N φ ρ φ' ρ' :
  nsl_dh_pred N φ ρ -∗
  nsl_dh_pred N φ' ρ' -∗
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
Definition nsl_dh_ready N si rl : iProp := ∀ φ ρ,
  nsl_dh_pred N φ ρ →
  term_token (si_share_of rl si) (↑nsl_dhN.@"ready") ={⊤}=∗
    ▷ φ si rl.

Lemma nsl_dh_ready_alloc N si rl φ ρ :
  nsl_dh_pred N φ ρ -∗
  φ si rl ={⊤}=∗
  □ nsl_dh_ready N si rl.
Proof.
iIntros "#N_φ φ_ts".
iMod (escrowI nroot with "φ_ts []") as "#?".
{ by iApply (term_token_switch (si_share_of rl si) (nsl_dhN.@"ready")). }
iIntros "!> !>  %φ' %ρ' #N_φ' ready".
iDestruct (nsl_dh_pred_agree with "N_φ N_φ'") as "[#φ_eq _]".
iSpecialize ("φ_eq" $! si rl).
iMod (escrowE with "[//] ready") as "res" => //.
iIntros "!> !>". by iRewrite -"φ_eq".
Qed.

Definition nsl_dh_key_share skI skR t : iProp :=
  (public skI ∨ public skR) ∧ ⌜length (elements (exps t)) = 1⌝.

Lemma exps_TExp1 a :
  negb (is_mul a) -> exps (TExp (TInt 0) a) = {[+ a +]}.
Proof. by move=> Nm; rewrite exps_TExp_expN // factors_Nmul. Qed.

Lemma exps_TExp2 a b :
  negb (is_mul a) -> negb (is_mul b) ->
  exps (TExp (TInt 0) (TMul {[+ a; b +]})) = SMS.make [a; b] [].
Proof.
move=> Nm_a Nm_b; rewrite exps_TExp_TMul // => u.
by case/SMS.elem_of_disj_union => /SMS.elem_of_singleton ->.
Qed.

Definition si_seed si : term :=
  Spec.of_list [Spec.pkey (si_init si); Spec.pkey (si_resp si);
                si_init_share si; si_resp_share si; si_secret si].

(* A hash, so that releasing the key does not reveal the shares. *)
Definition si_key si : senc_key :=
  SEncKey (THash (Spec.tag (Tag $ nsl_dhN.@"key") (si_seed si))).
Arguments si_key : simpl never.

Lemma session_agree si1 si2 :
  si_key si1 = si_key si2 →
  si1 = si2.
Proof.
case: si1 si2
  => [[skI1] [skR1] ga1 gb1 gab1] [[skI2] [skR2] ga2 gb2 gab2] /=.
rewrite /si_key /si_seed /=.
case=> /Spec.tag_inj [_] /Spec.of_list_inj.

by case=> /Spec.aenc_pkey_inj <- /Spec.aenc_pkey_inj <- <- <- <-.
Qed.

Lemma minted_si_key si : minted (si_key si) ⊣⊢ minted (si_seed si).
Proof. by rewrite /si_key minted_senc minted_THash minted_tag. Qed.

Lemma wp_session_key si (Ψ : val → iProp) :
  Ψ (repr (si_key si)) ⊢
  WP session_key (repr (si_seed si)) {{ Ψ }}.
Proof.
iIntros "post". wp_lam. wp_apply wp_tag. wp_apply wp_hash.
by wp_apply wp_derive_senc_key.
Qed.

(** The responder records on its share the usage of a session and the peer it
    answers. *)
Definition usage gb N : iProp :=
  term_meta gb (nsl_dhN.@"usage") N.

Definition resp_peer gb skI ga : iProp :=
  term_meta gb (nsl_dhN.@"peer") (skI, ga).

(** When [rl] completed [si], it could not rule out a forged message. *)
Definition compromised rl si : iProp :=
  term_meta (si_share_of rl si) (nsl_dhN.@"compromised") true.

#[global] Instance compromised_persistent rl si :
  Persistent (compromised rl si).
Proof. apply _. Qed.

#[global] Instance compromised_timeless rl si :
  Timeless (compromised rl si).
Proof. apply _. Qed.

(** A compromised session has a leaked long-term key, and the initiator then
    also makes the key public.  The responder cannot: it cannot tell a forged
    last message from a genuine one, and publishing its exponent would break
    the initiator's forward secrecy. *)
Definition session ρ rl si : iProp :=
  minted (si_key si) ∗
  □ (▷ □ ρ si → public (si_key si)) ∗
  (compromised rl si ∗ (public (si_init si) ∨ public (si_resp si)) ∗
     (if rl is Init then public (si_key si) else True) ∨
   □ (¬ compromised rl si) ∗ □ (public (si_key si) → ▷ ▷ □ ρ si)).

#[global] Instance session_persistent ρ rl si : Persistent (session ρ rl si).
Proof. by case: rl; apply _. Qed.

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

(** A DH exponent that leaks when [P] holds, and whose share leaks with a
    long-term key. *)
Definition dh_key skI skR P (a : nonce) : iProp :=
  minted a ∧
  □ (public a ↔ ▷ □ P) ∧
  □ (∀ t, exp_pred a t ↔ ▷ □ nsl_dh_key_share skI skR t).

#[global] Instance dh_key_persistent skI skR P a :
  Persistent (dh_key skI skR P a).
Proof. apply _. Qed.

Lemma wp_mk_dh_keys (T : gset term) skI skR (P : term → iProp)
    (Ψ : val → iProp) :
  cryptis_ctx -∗
  (∀ t, ⌜t ∈ T⌝ -∗ minted t) -∗
  (∀ (a : nonce),
    let ga := TExp (TInt 0) a in
    ⌜∀ t', t' ∈ T → ¬ subterm a t'⌝ -∗
    dh_key skI skR (P ga) a -∗
    term_token ga ⊤ -∗
    Ψ (repr (TNonce a, ga))) -∗
  WP mk_dh_keys #() {{ Ψ }}.
Proof.
iIntros "#ctx #minted_T post".
rewrite /mk_dh_keys. wp_lam.
wp_apply (wp_mk_nonce_freshN T (λ a, P (TExp (TInt 0) a))
            (nsl_dh_key_share skI skR)
            (λ a, {[TExp (TInt 0) a]})) => //.
- iIntros "%a".
  rewrite big_sepS_singleton minted_TExp //.
  rewrite minted_TInt /= bi.True_and.
  iModIntro. by iApply bi.equiv_iff.
iIntros "%a %fresh_a #m_a #s_a #dh_a _ token_ga".
rewrite big_sepS_singleton.
wp_pures.
wp_bind (tint _). iApply wp_tint.
wp_bind (texp _ _). iApply wp_texp.
wp_pures.
iApply ("post" with "[//] [] token_ga").
by do !iSplit.
Qed.

Lemma public_dh_share skI skR P (a : nonce) :
  dh_key skI skR P a -∗
  ▷ (public skI ∨ public skR) -∗
  public (TExp (TInt 0) a).
Proof.
iIntros "#(m_a & _ & #pred_a) corr".
have Nm : negb (is_mul a) by [].
iAssert (exp_pred a (TExp (TInt 0) a)) with "[corr]" as "#dp".
{ iAssert (▷ □ nsl_dh_key_share skI skR (TExp (TInt 0) a))%I
    with "[corr]" as "#ns".
  { iNext. iDestruct "corr" as "#corr".
    iModIntro. rewrite /nsl_dh_key_share. iSplit => //.
    iPureIntro.
    by rewrite (exps_TExp1 Nm) SMS.elements_singleton. }
  by iDestruct ("pred_a" $! (TExp (TInt 0) a) with "ns") as "$". }
rewrite public_TExp_iff //.
rewrite minted_TInt. do 3?[iSplit => //].
- by iRight.
- iIntros "!> _". by rewrite public_TInt.
Qed.

(** The DH secret leaks only with one of its exponents. *)
Lemma public_dh_secret skI skR P_a P_b (a b : nonce) :
  dh_key skI skR P_a a -∗
  dh_key skI skR P_b b -∗
  public (TExp (TExp (TInt 0) a) b) -∗
  ▷ □ (P_a ∨ P_b).
Proof.
iIntros "#(_ & s_a & pred_a) #(_ & s_b & pred_b) #p".
have Nm_a : negb (is_mul (TNonce a)) by [].
have Nm_b : negb (is_mul (TNonce b)) by [].
rewrite TExpA.
have ab : [TNonce a; TNonce b] ⊆+
    SMS.pos (exps (TExp (TInt 0) (TMul {[+ TNonce a; TNonce b +]}))).
  apply: Permutation_submseteq.
  by rewrite (exps_TExp2 Nm_a Nm_b) SMS.pos_make_nil_r.
have a_ab : TNonce a ∈ [TNonce a; TNonce b] by set_solver.
iPoseProof (public_exp_inv_gen a_ab ab with "p") as "(%c & %c_ab & H)".
rewrite elem_of_cons list_elem_of_singleton in c_ab.
iDestruct "H" as "[H|(%t3 & _ & %exps_sub & H)]".
- case: c_ab => ->.
  + iDestruct ("s_a" with "H") as "#P". iNext. iModIntro. by iLeft.
  + iDestruct ("s_b" with "H") as "#P". iNext. iModIntro. by iRight.
- iAssert (▷ □ nsl_dh_key_share skI skR t3)%I as "#ks".
  { by case: c_ab => ->; [iApply "pred_a"|iApply "pred_b"]. }
  iNext. iDestruct "ks" as "[_ %contra]". iExFalso. iPureIntro.
  move: contra (submseteq_length _ _ exps_sub).
  by rewrite SMS.elements_pos_neg length_app /=; lia.
Qed.

(* Message predicates for aenc *)

Definition msg1_pred skR m1 : iProp := ∃ ga skI,
  ⌜m1 = Spec.of_list [ga; Spec.pkey skI]⌝ ∧
  (public skI ∨ public skR → public ga).

Definition msg2_pred' skI skR ga gb N : iProp := ∃ (b : nonce),
  let si := SessInfo skI skR ga gb (TExp ga b) in
  ⌜gb = TExp (TInt 0) b⌝ ∧
  ⌜¬ subterm b ga⌝ ∧
  dh_key skI skR False b ∧
  resp_peer gb skI ga ∧
  usage gb N ∧
  nsl_dh_ready N si Init.

Definition msg2_pred skI m2 : iProp := ∃ ga gb skR N,
  ⌜m2 = Spec.of_list [ga; gb; Spec.pkey skR; Tag N]⌝ ∧
  msg2_pred' skI skR ga gb N.

(** The initiator vouches for the session that the responder recorded on its
    share: the initiator's exponent is honest, and the gift is escrowed. *)
Definition msg3_pred skR gb : iProp := ∀ skI ga (b : nonce),
  let si := SessInfo skI skR ga gb (TExp ga b) in
  ⌜gb = TExp (TInt 0) b⌝ →
  resp_peer gb skI ga →
  ∃ a : nonce, ⌜ga = TExp (TInt 0) a⌝ ∧
    dh_key skI skR (compromised Init si) a ∧
    □ (¬ compromised Init si) ∧
    ∃ N, usage gb N ∧ nsl_dh_ready N si Resp.

Definition key_pred t : iProp :=
  ∃ si N φ ρ, ⌜t = si_seed si⌝ ∗ usage (si_resp_share si) N ∗
    nsl_dh_pred N φ ρ ∗ □ ρ si.

Definition nsl_dh_ctx : iProp :=
  aenc_pred (nsl_dhN.@"m1") msg1_pred ∧
  aenc_pred (nsl_dhN.@"m2") msg2_pred ∧
  aenc_pred (nsl_dhN.@"m3") msg3_pred ∧
  hash_pred (nsl_dhN.@"key") key_pred.

Lemma nsl_dh_ctx_alloc E :
  ↑nsl_dhN ⊆ E →
  seal_pred_token AENC E -∗
  hash_pred_token E ==∗
  nsl_dh_ctx ∗ seal_pred_token AENC (E ∖ ↑nsl_dhN) ∗
  hash_pred_token (E ∖ ↑nsl_dhN).
Proof.
iIntros (sub) "token h_token".
rewrite (seal_pred_token_difference _ (↑nsl_dhN) E) //.
iDestruct "token" as "[token token']". iFrame.
iMod (aenc_pred_set (N := nsl_dhN.@"m1") msg1_pred with "token")
  as "[#H1 token]"; try solve_ndisj.
iMod (aenc_pred_set (N := nsl_dhN.@"m2") msg2_pred with "token")
  as "[#H2 token]"; try solve_ndisj.
iMod (aenc_pred_set (N := nsl_dhN.@"m3") msg3_pred with "token")
  as "[#H3 token]"; try solve_ndisj.
iMod (hash_pred_set (nsl_dhN.@"key") key_pred with "h_token")
  as "[#H4 h_token]"; try solve_ndisj.
iModIntro. iSplit; first by do !iSplit.
iApply (hash_pred_token_drop with "h_token"). solve_ndisj.
Qed.

#[global] Instance nsl_dh_ctx_persistent : Persistent nsl_dh_ctx.
Proof. apply _. Qed.

(** The usage on the responder's share finds the release condition. *)
Lemma key_release N φ ρ si :
  nsl_dh_ctx -∗
  nsl_dh_pred N φ ρ -∗
  usage (si_resp_share si) N -∗
  minted (si_key si) -∗
  □ (▷ □ ρ si → public (si_key si)).
Proof.
iIntros "#(_ & _ & _ & key) #N_φ #use #m_k !> #rel".
rewrite /si_key public_senc_key.
iApply (public_THashIS with "key [] []").
- by iEval (rewrite minted_si_key) in "m_k".
- iNext; iModIntro; iExists si, N, φ, ρ. by do !iSplit.
Qed.

(** Both exponents are honest, so only release can publish the key. *)
Lemma honest_session skI skR N φ ρ (a b : nonce) :
  let ga := TExp (TInt 0) a in
  let gb := TExp (TInt 0) b in
  let si := SessInfo skI skR ga gb (TExp ga b) in
  nsl_dh_ctx -∗
  nsl_dh_pred N φ ρ -∗
  dh_key skI skR (compromised Init si) a -∗
  dh_key skI skR False b -∗
  □ (¬ compromised Init si) -∗
  usage gb N -∗
  minted (si_key si) -∗
  □ (▷ □ ρ si → public (si_key si)) ∗
  □ (public (si_key si) → ▷ ▷ □ ρ si).
Proof.
move=> ga gb si.
iIntros "#ctx #N_φ #dh_a #dh_b #nc #use #m_k".
iSplit; first by iApply (key_release _ _ _ si with "ctx N_φ use m_k").

iDestruct "ctx" as "(_ & _ & _ & key)".
iIntros "!> #p_k".
iEval (rewrite /si_key public_senc_key) in "p_k".
iDestruct (public_THashE with "key p_k") as "[p_t | [_ #rel]]".
- iEval (rewrite /si_seed public_of_list /=) in "p_t".
  iDestruct "p_t" as "(_ & _ & _ & _ & p_gab & _)".
  iPoseProof (public_dh_secret with "dh_a dh_b p_gab") as "f".
  iNext. iDestruct "f" as "#[c|[]]".
  by iDestruct ("nc" with "c") as "[]".
- iNext.
  iDestruct "rel" as "(%si' & %N' & %φ' & %ρ' & %e & #use' & #N_φ' & #r)".
  have <- : si = si' by apply: session_agree; rewrite /si_key e.
  iPoseProof (term_meta_agree with "use use'") as "<-".
  iDestruct (nsl_dh_pred_agree with "N_φ N_φ'") as "[_ #ρ_eq]".
  iSpecialize ("ρ_eq" $! si).
  iNext. by iRewrite "ρ_eq".
Qed.

End Verif.

Arguments nsl_dh_ctx_alloc {Σ _ _ _} E.

Lemma nsl_dhGS_alloc `{!heapGS Σ, !cryptisGS Σ} E :
  ↑nsl_dhN ⊆ E →
  nsl_dhGpreS Σ →
  seal_pred_token AENC E -∗
  hash_pred_token E ={⊤}=∗ ∃ (H : nsl_dhGS Σ),
    nsl_dh_ctx ∗ nsl_dh_token ⊤ ∗
    seal_pred_token AENC (E ∖ ↑nsl_dhN) ∗
    hash_pred_token (E ∖ ↑nsl_dhN).
Proof.
iIntros "% %Hpre token h_token".
iMod gmeta_token_alloc as (γ_meta) "own".
set nsl_dhGS0 := {| nsl_dh_inG := Hpre; nsl_dh_name := γ_meta |} : nsl_dhGS Σ.
iExists nsl_dhGS0.
iMod (nsl_dh_ctx_alloc with "token h_token") as "(#H & ? & ?)" => //.
by iFrame.
Qed.

Arguments nsl_dhGS_alloc {Σ _ _ E}.
Arguments nsl_dh_pred_set {Σ _} N φ ρ E.
