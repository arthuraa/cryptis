From cryptis Require Import lib.
From mathcomp Require Import ssreflect.
From mathcomp Require order.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap reservation_map.
From iris.base_logic.lib Require Import invariants saved_prop.
From iris.program_logic Require Import atomic.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import nondet_bool ticket_lock.
From cryptis Require Import term cryptis.
From cryptis.primitives Require Import notations pre_term comp simple.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Existing Instance cryptisGS_tlock.
Local Existing Instance ticket_lock.

Definition get_chan : val := λ: "c" "lock", rec: "loop" <> :=
  let: "n" := nondet_nat #() in
  acquire "lock";;
  let: "ts" := !"c" in
  release "lock";;
  match: get_list "ts" "n" with
    NONE => "loop" #()
  | SOME "t" => "t"
  end.

Definition put_chan : val := λ: "c" "lock" "t",
  acquire "lock";;
  "c" <- "t" :: !"c";;
  release "lock".

Definition mk_channel : val := λ: <>,
  let: "c" := ref []%V in
  let: "lock" := newlock #() in
  (put_chan "c" "lock", get_chan "c" "lock").

Definition send : val := λ: "c", Fst "c".
Definition recv : val := λ: "c", Snd "c" #().

Definition mk_nonce : val := λ: <>,
  let: "n" := ref #() in
  (#TOp0_tag, (#TNonce_tag, "n")).

Definition mk_aenc_key : val := λ: <>,
  let: "n" := mk_nonce #() in
  derive_aenc_key "n".

Definition mk_sign_key : val := λ: <>,
  let: "n" := mk_nonce #() in
  derive_sign_key "n".

Definition mk_senc_key : val := λ: <>,
  let: "n" := mk_nonce #() in
  derive_senc_key "n".

Section Proofs.

Context `{!heapGS Σ, !cryptisGS Σ}.
Notation nonce := loc.

Implicit Types E : coPset.
Implicit Types a : nonce.
Implicit Types t : term.
Implicit Types v : val.
Implicit Types Φ : prodO locO termO -n> iPropO Σ.
Implicit Types Ψ : val → iProp Σ.

Definition channel c : iProp Σ :=
  ∃ (sf rf : val), ⌜c = (sf, rf)%V⌝ ∗
    □ (∀ t Ψ, public t -∗ Ψ #() -∗ WP sf t {{ Ψ }}) ∗
    □ (∀ Ψ, (∀ t, public t -∗ Ψ t) -∗ WP rf #() {{ Ψ }}).

Global Instance channel_persistent c : Persistent (channel c).
Proof. apply _. Qed.

Definition chan_inv (c : loc) : iProp Σ :=
  ∃ ts : list term, c ↦ repr ts ∗ [∗ list] t ∈ ts, public t.

Lemma wp_mk_channel Ψ :
  (∀ c, channel c -∗ Ψ c) ⊢
  WP mk_channel #() {{ Ψ }}.
Proof.
iIntros "post".
wp_lam; wp_apply (wp_nil (A := term)).
wp_alloc c as "cP"; wp_pures.
wp_apply (newlock_spec (chan_inv c) with "[cP]").
  by iExists []; iSplit => //.
iIntros "%lk %γ #lkP"; rewrite /get_chan /put_chan; wp_pures.
iModIntro; iApply "post". clear Ψ. iExists _, _; do 2!iSplit => //.
- iIntros "!> %t %Ψ #p_t post".
  wp_pures. wp_apply acquire_spec => //. iIntros "[locked inv]".
  iDestruct "inv" as (ts) "[c_ts #tsP]".
  wp_pures; wp_load.
  wp_apply wp_cons. wp_store.
  wp_apply (release_spec with "[$locked c_ts]").
  { iSplit => //. iExists (t :: ts). iFrame.
    rewrite big_sepL_cons. eauto. }
  by iIntros "_".
- iLöb as "IH".
  iIntros "!> %Ψ post".
  wp_rec. wp_apply wp_nondet_nat. iIntros "%n". wp_pures.
  wp_apply (acquire_spec with "lkP") => //.
  iIntros "[locked inv]".
  iDestruct "inv" as (ts) "[c_ts #tsP]".
  wp_pures; wp_load.
  wp_pures; wp_apply (release_spec with "[$locked c_ts]").
  { iSplit => //. iExists ts; eauto. }
  iIntros "_". wp_pures. wp_apply wp_get_list.
  case ts_n: (ts !! n) => [t'|].
  { wp_pures. iApply "post". rewrite big_sepL_forall. by iApply "tsP". }
  wp_pure _. wp_pure _. wp_pure _.
  iApply ("IH" with "post").
Qed.

Lemma wp_send c t Ψ :
  channel c -∗
  ▷ public t -∗
  Ψ #() -∗
  WP send c t {{ Ψ }}.
Proof.
iDestruct 1 as (sf cf) "#(-> & H & _)".
iIntros "#??"; rewrite /send; wp_pures.
by iApply "H".
Qed.

Lemma wp_recv c Ψ :
  channel c -∗
  (∀ t, public t -∗ Ψ t) -∗
  WP recv c {{ Ψ }}.
Proof.
iDestruct 1 as (sf cf) "#(-> & _ & H)".
iIntros "?"; rewrite /recv; wp_pures.
by iApply "H".
Qed.

Lemma twp_mk_nonce_gen (P Q : term → iProp Σ) E Ψ (Φ : term → iProp Σ) :
  (∀ t, (minted t -∗ False) ∧
        (|==> minted t ∗
              □ (public t ↔ ▷ □ P t) ∗
              □ (∀ t', dh_pred t t' ↔ ▷ □ Q t')) ={E}=∗
        minted t ∗
        □ (public t ↔ ▷ □ P t) ∗
        □ (∀ t', dh_pred t t' ↔ ▷ □ Q t') ∗
        Φ t) -∗
  (∀ t, ⌜is_nonce t⌝ -∗
        minted t -∗
        □ (public t ↔ ▷ □ P t) -∗
        □ (∀ t', dh_pred t t' ↔ ▷ □ Q t') -∗
        Φ t -∗
        Ψ t) -∗
  WP mk_nonce #()%V @ E [{ Ψ }].
Proof.
rewrite /mk_nonce; iIntros "mint post".
wp_pures; wp_bind (ref _)%E; iApply twp_alloc=> //.
iIntros (a) "[_ token]".
iPoseProof (nonce_alloc P Q with "token") as "fresh".
iPoseProof ("mint" with "fresh") as ">(#? & #? & #? & ?)".
iSpecialize ("post" $! (TNonce a)).
wp_pures. rewrite val_of_term_unseal /=.
iApply ("post" with "[] [] [] [$]"); eauto.
Qed.

Lemma wp_mk_nonce_gen (P Q : term → iProp Σ) E Ψ (Φ : term → iProp Σ) :
  (∀ t, (minted t -∗ False) ∧
        (|==> minted t ∗
              □ (public t ↔ ▷ □ P t) ∗
              □ (∀ t', dh_pred t t' ↔ ▷ □ Q t')) ={E}=∗
        minted t ∗
        □ (public t ↔ ▷ □ P t) ∗
        □ (∀ t', dh_pred t t' ↔ ▷ □ Q t') ∗
        Φ t) -∗
  (∀ t, ⌜is_nonce t⌝ -∗
        minted t -∗
        □ (public t ↔ ▷ □ P t) -∗
        □ (∀ t', dh_pred t t' ↔ ▷ □ Q t') -∗
        Φ t -∗
        Ψ t) -∗
  WP mk_nonce #()%V @ E {{ Ψ }}.
Proof.
iIntros "H1 H2". iApply twp_wp.
iApply (twp_mk_nonce_gen with "H1 H2").
Qed.

Lemma twp_mk_nonce_freshN (T : gset term) (P Q : term → iProp Σ) (T' : term → gset term) Ψ :
  cryptis_ctx -∗
  (∀ t, ⌜t ∈ T⌝ -∗ minted t) -∗
  (∀ t, [∗ set] t' ∈ T' t, □ (minted t ↔ minted t')) -∗
  (∀ t, ⌜∀ t', t' ∈ T → ¬ subterm t t'⌝ -∗
        ⌜is_nonce t⌝ -∗
        minted t -∗
        □ (public t ↔ ▷ □ P t) -∗
        □ (∀ t', dh_pred t t' ↔ ▷ □ Q t') -∗
        ([∗ set] t' ∈ T' t, term_token t' ⊤) -∗
        Ψ t) -∗
  WP mk_nonce #()%V [{ Ψ }].
Proof.
iIntros "#ctx minted_T #minted_T' post".
iApply (twp_mk_nonce_gen P Q ⊤ _
          (λ t, ⌜∀ t', t' ∈ T → ¬ subterm t t'⌝ ∗
          [∗ set] t' ∈ T' t, term_token t' ⊤)%I
         with "[minted_T] [post]").
{ iIntros "%t fresh".
  iAssert (⌜∀ t', t' ∈ T → ¬ subterm t t'⌝)%I as "%fresh".
  { iIntros "%t' %t'_T %t_t'".
    iPoseProof ("minted_T" $! t' with "[//]") as "#minted_t'".
    iPoseProof (subterm_minted t_t' with "minted_t'") as "minted_t".
    iDestruct "fresh" as "[fresh _]".
    by iApply "fresh". }
  iMod (term_token_alloc (T' t)
          (minted t -∗ False)
          (minted t ∗ □ (public t ↔ ▷ □ P t) ∗
           □ (∀ t', dh_pred t t' ↔ ▷ □ Q t'))
          with "ctx [] [] [fresh]") as "(post & token)" => //.
  - iIntros "%t' %t'_t contra minted_t'". iApply "contra".
    iSpecialize ("minted_T'" $! t).
    rewrite big_sepS_delete //.
    iDestruct "minted_T'" as "[#e _]". by iApply "e".
  - iIntros "%t' %t'_t (minted_t & _)".
    iSpecialize ("minted_T'" $! t).
    rewrite big_sepS_delete //.
    iDestruct "minted_T'" as "[#e _]". by iApply "e".
  - iSplit.
    + by iDestruct "fresh" as "[fresh _]".
    + by iDestruct "fresh" as "[_ >fresh]".
  iFrame. do !iModIntro.
  iDestruct "post" as "(? & ? & ?)". eauto. }
iIntros "% ? ? ? ? [? ?]".
iApply ("post" with "[$] [$] [$] [$] [$] [$]").
Qed.

Lemma wp_mk_nonce_freshN (T : gset term) P Q (T' : term → gset term) Ψ :
  cryptis_ctx -∗
  (∀ t, ⌜t ∈ T⌝ -∗ minted t) -∗
  (∀ t, [∗ set] t' ∈ T' t, □ (minted t ↔ minted t')) -∗
  (∀ t, ⌜∀ t', t' ∈ T → ¬ subterm t t'⌝ -∗
        ⌜is_nonce t⌝ -∗
        minted t -∗
        □ (public t ↔ ▷ □ P t) -∗
        □ (∀ t', dh_pred t t' ↔ ▷ □ Q t') -∗
        ([∗ set] t' ∈ T' t, term_token t' ⊤) -∗
        Ψ t) -∗
  WP mk_nonce #()%V {{ Ψ }}.
Proof.
iIntros "#ctx H1 H2 H3".
by iApply twp_wp; iApply (twp_mk_nonce_freshN with "[//] H1 H2 H3").
Qed.

Lemma twp_mk_nonce_fresh (T : gset term) (P Q : term → iProp Σ) Ψ :
  cryptis_ctx -∗
  (∀ t, ⌜t ∈ T⌝ -∗ minted t) -∗
  (∀ t, ⌜∀ t', t' ∈ T → ¬ subterm t t'⌝ -∗
        ⌜is_nonce t⌝ -∗
        minted t -∗
        □ (public t ↔ ▷ □ P t) -∗
        □ (∀ t', dh_pred t t' ↔ ▷ □ Q t') -∗
        term_token t ⊤ -∗
        Ψ t) -∗
  WP mk_nonce #()%V [{ Ψ }].
Proof.
iIntros "#ctx minted_T post".
iApply (twp_mk_nonce_freshN T P Q (λ t : term, {[t]}) _
         with "[//] minted_T [] [post]") => //.
{ iIntros "%t". rewrite big_sepS_singleton. iModIntro.
  iSplit; by iIntros "?". }
iIntros "% ? ? ? ? ?".
rewrite big_sepS_singleton.
by iApply ("post" with "[$] [$] [$] [$] [$]").
Qed.

Lemma wp_mk_nonce_fresh (T : gset term) P Q Ψ :
  cryptis_ctx -∗
  (∀ t, ⌜t ∈ T⌝ -∗ minted t) -∗
  (∀ t, ⌜∀ t', t' ∈ T → ¬ subterm t t'⌝ -∗
        ⌜is_nonce t⌝ -∗
        minted t -∗
        □ (public t ↔ ▷ □ P t) -∗
        □ (∀ t', dh_pred t t' ↔ ▷ □ Q t') -∗
        term_token t ⊤ -∗
        Ψ t) -∗
  WP mk_nonce #()%V {{ Ψ }}.
Proof.
iIntros "#ctx H1 H2".
by iApply twp_wp; iApply (twp_mk_nonce_fresh with "[//] H1 H2").
Qed.

Lemma twp_mk_nonce (P Q : term → iProp Σ) Ψ :
  cryptis_ctx -∗
  (∀ t, ⌜is_nonce t⌝ -∗
        minted t -∗
        □ (public t ↔ ▷ □ P t) -∗
        □ (∀ t', dh_pred t t' ↔ ▷ □ Q t') -∗
        term_token t ⊤ -∗
        Ψ t) -∗
  WP mk_nonce #()%V [{ Ψ }].
Proof.
iIntros "#ctx post". iApply (twp_mk_nonce_fresh ∅ P Q) => //.
- iIntros "%". rewrite elem_of_empty. iDestruct 1 as "[]".
- iIntros "% _". iApply "post".
Qed.

Lemma wp_mk_nonce (P Q : term → iProp Σ) Ψ :
  cryptis_ctx -∗
  (∀ t, ⌜is_nonce t⌝ -∗
        minted t -∗
        □ (public t ↔ ▷ □ P t) -∗
        □ (∀ t', dh_pred t t' ↔ ▷ □ Q t') -∗
        term_token t ⊤ -∗
        Ψ t) -∗
  WP mk_nonce #()%V {{ Ψ }}.
Proof.
iIntros "#ctx H".
by iApply twp_wp; iApply (twp_mk_nonce with "[//] H").
Qed.

Lemma twp_mk_aenc_key Ψ :
  cryptis_ctx -∗
  (∀ sk : aenc_key,
      minted sk -∗
      secret sk -∗
      term_token sk ⊤ -∗
      Ψ sk) -∗
  WP mk_aenc_key #() [{ Ψ }].
Proof.
iIntros "#ctx post". iMod pending_alloc as (γ) "pending".
rewrite /mk_aenc_key. wp_pures.
wp_bind (mk_nonce _).
iApply (twp_mk_nonce_freshN ∅ (λ _, shot γ 1) (λ _, False%I)
  (λ t, {[(AEncKey t) : term]})) => //.
- iIntros "% ?". by rewrite elem_of_empty.
- iIntros "%t". rewrite [term_of_aenc_key]unlock big_sepS_singleton minted_TKey.
  iModIntro. by iSplit; iIntros "?".
iIntros "%t %fresh % #m_t #s_t _ token".
rewrite big_sepS_singleton.
pose sk := AEncKey t.
iAssert (public sk ↔ ▷ □ shot γ 1)%I as "s_sk".
{ by rewrite public_adec_key. }
rewrite bi.intuitionistic_intuitionistically.
iPoseProof (secret_alloc with "s_sk pending") as "tP".
wp_pures. wp_lam. iApply twp_key.
rewrite [term_of_aenc_key]unlock /=.
iApply ("post" $! (AEncKey _) with "[] [$] [$]").
by rewrite minted_TKey.
Qed.

Lemma wp_mk_aenc_key Ψ :
  cryptis_ctx -∗
  (∀ sk : aenc_key,
      minted sk -∗
      secret sk -∗
      term_token sk ⊤ -∗
      Ψ sk) -∗
  WP mk_aenc_key #() {{ Ψ }}.
Proof.
iIntros "#? ?". iApply twp_wp. by wp_apply twp_mk_aenc_key.
Qed.

Lemma twp_mk_sign_key Ψ :
  cryptis_ctx -∗
  (∀ sk : sign_key,
      minted sk -∗
      secret sk -∗
      term_token sk ⊤ -∗
      Ψ sk) -∗
  WP mk_sign_key #() [{ Ψ }].
Proof.
iIntros "#ctx post". iMod pending_alloc as (γ) "pending".
rewrite /mk_sign_key. wp_pures.
wp_bind (mk_nonce _).
iApply (twp_mk_nonce_freshN ∅ (λ _, shot γ 1) (λ _, False%I)
  (λ t, {[(SignKey t) : term]})) => //.
- iIntros "% ?". by rewrite elem_of_empty.
- iIntros "%t". rewrite [term_of_sign_key]unlock big_sepS_singleton minted_TKey.
  iModIntro. by iSplit; iIntros "?".
iIntros "%t %fresh % #m_t #s_t _ token".
rewrite big_sepS_singleton.
pose sk := SignKey t.
iAssert (public sk ↔ ▷ □ shot γ 1)%I as "s_sk".
{ by rewrite public_sign_key. }
rewrite bi.intuitionistic_intuitionistically.
iPoseProof (secret_alloc with "s_sk pending") as "tP".
wp_pures. wp_lam. iApply twp_key.
rewrite [term_of_sign_key]unlock /=.
iApply ("post" $! (SignKey _) with "[] [$] [$]").
by rewrite minted_TKey.
Qed.

Lemma wp_mk_sign_key Ψ :
  cryptis_ctx -∗
  (∀ sk : sign_key,
      minted sk -∗
      secret sk -∗
      term_token sk ⊤ -∗
      Ψ sk) -∗
  WP mk_sign_key #() {{ Ψ }}.
Proof.
iIntros "#? ?". iApply twp_wp. by wp_apply twp_mk_sign_key.
Qed.

Lemma twp_mk_senc_key Ψ :
  cryptis_ctx -∗
  (∀ k : senc_key,
      minted k -∗
      secret k -∗
      term_token k ⊤ -∗
      Ψ k) -∗
  WP mk_senc_key #() [{ Ψ }].
Proof.
iIntros "#ctx post". iMod pending_alloc as (γ) "pending".
rewrite /mk_senc_key. wp_pures.
wp_bind (mk_nonce _).
iApply (twp_mk_nonce_freshN ∅ (λ _, shot γ 1) (λ _, False%I)
  (λ t, {[(SEncKey t) : term]})) => //.
- iIntros "% ?". by rewrite elem_of_empty.
- iIntros "%t". rewrite [term_of_senc_key]unlock big_sepS_singleton minted_TKey.
  iModIntro. by iSplit; iIntros "?".
iIntros "%t %fresh % #m_t #s_t _ token".
rewrite big_sepS_singleton.
pose sk := SEncKey t.
iAssert (public sk ↔ ▷ □ shot γ 1)%I as "s_sk".
{ by rewrite public_senc_key. }
rewrite bi.intuitionistic_intuitionistically.
iPoseProof (secret_alloc with "s_sk pending") as "tP".
wp_pures. wp_lam. iApply twp_key.
rewrite [term_of_senc_key]unlock /=.
iApply ("post" $! (SEncKey _) with "[] [$] [$]").
by rewrite minted_TKey.
Qed.

Lemma wp_mk_senc_key Ψ :
  cryptis_ctx -∗
  (∀ k : senc_key,
      minted k -∗
      secret k -∗
      term_token k ⊤ -∗
      Ψ k) -∗
  WP mk_senc_key #() {{ Ψ }}.
Proof.
iIntros "#? ?". iApply twp_wp. by wp_apply twp_mk_senc_key.
Qed.

Lemma twp_aenc (sk : aenc_key) N t φ Ψ :
  aenc_pred N φ -∗
  minted sk -∗
  minted t -∗
  public t ∨ □ φ sk t ∧ □ (public sk → public t) -∗
  (∀ m, public m → Ψ m) -∗
  WP aenc (Spec.pkey sk) (Tag N) t [{ Ψ }].
Proof.
iIntros "#? #? #? #inv post".
wp_lam. wp_pures. wp_apply twp_enc. iApply "post".
iDestruct "inv" as "[p_t|[??]]".
- iApply public_TSealIP.
  + by iApply public_aenc_key.
  + by rewrite public_tag.
- iApply public_aencIS => //.
Qed.

Lemma wp_aenc (sk : aenc_key) N t φ Ψ :
  aenc_pred N φ -∗
  minted sk -∗
  minted t -∗
  public t ∨ □ φ sk t ∧ □ (public sk → public t) -∗
  (∀ m, public m → Ψ m) -∗
  WP aenc (Spec.pkey sk) (Tag N) t {{ Ψ }}.
Proof.
iIntros "#? #? #? #? ?".
iApply twp_wp. by wp_apply twp_aenc.
Qed.

Lemma wp_adec (sk : aenc_key) N m φ Ψ :
  aenc_pred N φ -∗
  public m -∗
  (∀ t, minted t -∗
        public t ∨ □ φ sk t ∧ □ (public sk → public t) -∗
        Ψ (SOMEV t)) ∧
  Ψ NONEV -∗
  WP adec sk (Tag N) m {{ Ψ }}.
Proof.
iIntros "#? #p_m post".
wp_lam. wp_pure _ credit:"c". wp_pures. iApply wp_fupd. wp_apply wp_dec.
case: Spec.decP => [k_t t /Spec.open_key_aencK -> ->|]; last first.
{ iDestruct "post" as "[_ post]". iApply "post". }
iPoseProof (public_aencE with "p_m [//]") as "[? [p_t|[#inv #p_t]]]".
- iApply "post" => //. by eauto.
- iMod (lc_fupd_elim_later_pers with "c inv") as "#?".
  iApply "post" => //. by eauto.
Qed.

Lemma twp_senc (sk : senc_key) N t φ Ψ :
  senc_pred N φ -∗
  minted sk -∗
  minted t -∗
  public sk ∨ □ φ sk t -∗
  □ (public sk → public t) -∗
  (∀ m, public m → Ψ m) -∗
  WP senc sk (Tag N) t [{ Ψ }].
Proof.
iIntros "#? #? #? #inv #p_t post".
wp_lam. wp_pures. wp_apply twp_enc. iApply "post".
iDestruct "inv" as "[p_sk|inv]".
- iApply public_TSealIP => //.
  rewrite public_tag. by iApply "p_t".
- by iApply public_sencIS => //.
Qed.

Lemma wp_senc (sk : senc_key) N t φ Ψ :
  senc_pred N φ -∗
  minted sk -∗
  minted t -∗
  public sk ∨ □ φ sk t -∗
  □ (public sk → public t) -∗
  (∀ m, public m → Ψ m) -∗
  WP senc sk (Tag N) t {{ Ψ }}.
Proof. by iIntros "#?#?#?#?#??"; iApply twp_wp; iApply twp_senc. Qed.

Lemma wp_sdec (sk : senc_key) N m φ Ψ :
  senc_pred N φ -∗
  public m -∗
  (∀ t, minted t -∗
        public sk ∨ □ φ sk t -∗
        □ (public sk → public t) -∗
        Ψ (SOMEV t)) ∧
  Ψ NONEV -∗
  WP sdec sk (Tag N) m {{ Ψ }}.
Proof.
iIntros "#? #p_m post".
wp_lam. wp_pure _ credit:"c". wp_pures. iApply wp_fupd. wp_apply wp_dec.
case: Spec.decP => [k_t t /Spec.open_key_sencK -> ->|]; last first.
{ iDestruct "post" as "[_ post]". iApply "post". }
iPoseProof (public_sencE with "p_m [//]") as "(? & [p_k|inv] & #p_t)".
- iApply "post" => //. by eauto.
- iMod (lc_fupd_elim_later_pers with "c inv") as "#?".
  iApply "post" => //. by eauto.
Qed.

Lemma twp_sign (sk : sign_key) N t φ Ψ :
  sign_pred N φ -∗
  minted sk -∗
  public t -∗
  public sk ∨ □ φ sk t -∗
  (∀ m, public m → Ψ m) -∗
  WP sign sk (Tag N) t [{ Ψ }].
Proof.
iIntros "#? #? #? #inv post".
wp_lam. wp_pures. wp_apply twp_enc. iApply "post".
iDestruct "inv" as "[p_t|#?]".
- iApply public_TSealIP => //.
  by rewrite public_tag.
- by iApply public_signIS => //.
Qed.

Lemma wp_sign (sk : sign_key) N t φ Ψ :
  sign_pred N φ -∗
  minted sk -∗
  public t -∗
  public sk ∨ □ φ sk t -∗
  (∀ m, public m → Ψ m) -∗
  WP sign sk (Tag N) t {{ Ψ }}.
Proof.
iIntros "#? #? #? #? ?".
iApply twp_wp. by wp_apply twp_sign.
Qed.

Lemma wp_verify (sk : sign_key) N m φ Ψ :
  sign_pred N φ -∗
  public m -∗
  (∀ t, public t -∗
        public sk ∨ □ φ sk t -∗
        Ψ (SOMEV t)) ∧
  Ψ NONEV -∗
  WP verify (Spec.pkey sk) (Tag N) m {{ Ψ }}.
Proof.
iIntros "#? #p_m post".
wp_lam. wp_pure _ credit:"c". wp_pures. iApply wp_fupd. wp_apply wp_dec.
case: Spec.decP => [k_t t /Spec.open_key_signK -> ->|]; last first.
{ iDestruct "post" as "[_ post]". iApply "post". }
iPoseProof (public_signE with "p_m [//]") as "[? [p_t|#inv]]".
- iApply "post" => //. by eauto.
- iMod (lc_fupd_elim_later_pers with "c inv") as "#?".
  iApply "post" => //. by eauto.
Qed.

Lemma twp_is_aenc_key pk Ψ :
  minted pk -∗
  (∀ sk : aenc_key, ⌜pk = Spec.pkey sk⌝ -∗ minted sk -∗ Ψ #true) ∧ Ψ #false -∗
  WP is_aenc_key pk [{ Ψ }].
Proof.
iIntros "#m_pk post".
wp_lam. wp_apply (twp_has_key_type AEnc).
case: pk; try by move=> *; iDestruct "post" as "[_ post]".
move=> kt t.
case: kt; try by iDestruct "post" as "[_ post]".
iDestruct "post" as "[post _]".
by iApply ("post" $! (AEncKey t)) => //;
rewrite [term_of_aenc_key]unlock // !minted_TKey.
Qed.

Lemma wp_is_aenc_key pk Ψ :
  minted pk -∗
  (∀ sk : aenc_key, ⌜pk = Spec.pkey sk⌝ -∗ minted sk -∗ Ψ #true) ∧ Ψ #false -∗
  WP is_aenc_key pk {{ Ψ }}.
Proof.
by iIntros "H1 H2"; iApply twp_wp;
iApply (twp_is_aenc_key with "H1 H2").
Qed.

Lemma twp_is_adec_key sk Ψ :
  minted sk -∗
  (∀ sk' : aenc_key, ⌜sk = sk'⌝ -∗ Ψ #true) ∧ Ψ #false -∗
  WP is_adec_key sk [{ Ψ }].
Proof.
iIntros "#m_pk post".
wp_lam. wp_apply (twp_has_key_type ADec).
case: sk; try by move=> *; iDestruct "post" as "[_ post]".
move=> kt t.
case: kt; try by iDestruct "post" as "[_ post]".
iDestruct "post" as "[post _]".
by iApply ("post" $! (AEncKey t)) => //;
rewrite [term_of_aenc_key]unlock // !minted_TKey.
Qed.

Lemma wp_is_adec_key sk Ψ :
  minted sk -∗
  (∀ sk' : aenc_key, ⌜sk = sk'⌝ -∗ Ψ #true) ∧ Ψ #false -∗
  WP is_adec_key sk {{ Ψ }}.
Proof.
by iIntros "H1 H2"; iApply twp_wp;
iApply (twp_is_adec_key with "H1 H2").
Qed.

Lemma twp_is_senc_key k Ψ :
  minted k -∗
  (∀ k' : senc_key, ⌜k = k'⌝ -∗ Ψ #true) ∧ Ψ #false -∗
  WP is_senc_key k [{ Ψ }].
Proof.
iIntros "#m_pk post".
wp_lam. wp_apply (twp_has_key_type SEnc).
case: k; try by move=> *; iDestruct "post" as "[_ post]".
move=> kt t.
case: kt; try by iDestruct "post" as "[_ post]".
iDestruct "post" as "[post _]".
by iApply ("post" $! (SEncKey t)) => //;
rewrite [term_of_senc_key]unlock // !minted_TKey.
Qed.

Lemma wp_is_senc_key k Ψ :
  minted k -∗
  (∀ k' : senc_key, ⌜k = k'⌝ -∗ Ψ #true) ∧ Ψ #false -∗
  WP is_senc_key k {{ Ψ }}.
Proof.
by iIntros "H1 H2"; iApply twp_wp;
iApply (twp_is_senc_key with "H1 H2").
Qed.

Lemma twp_is_verify_key pk Ψ :
  minted pk -∗
  (∀ sk : sign_key, ⌜pk = Spec.pkey sk⌝ -∗ minted sk -∗ Ψ #true) ∧ Ψ #false -∗
  WP is_verify_key pk [{ Ψ }].
Proof.
iIntros "#m_pk post".
wp_lam. wp_apply (twp_has_key_type Verify).
case: pk; try by move=> *; iDestruct "post" as "[_ post]".
move=> kt t.
case: kt; try by iDestruct "post" as "[_ post]".
iDestruct "post" as "[post _]".
by iApply ("post" $! (SignKey t)) => //;
rewrite [term_of_sign_key]unlock // !minted_TKey.
Qed.

Lemma wp_is_verify_key pk Ψ :
  minted pk -∗
  (∀ sk : sign_key, ⌜pk = Spec.pkey sk⌝ -∗ minted sk -∗ Ψ #true) ∧ Ψ #false -∗
  WP is_verify_key pk {{ Ψ }}.
Proof.
by iIntros "H1 H2"; iApply twp_wp;
iApply (twp_is_verify_key with "H1 H2").
Qed.

Lemma twp_is_sign_key sk Ψ :
  minted sk -∗
  (∀ sk' : sign_key, ⌜sk = sk'⌝ -∗ Ψ #true) ∧ Ψ #false -∗
  WP is_sign_key sk [{ Ψ }].
Proof.
iIntros "#m_pk post".
wp_lam. wp_apply (twp_has_key_type Sign).
case: sk; try by move=> *; iDestruct "post" as "[_ post]".
move=> kt t.
case: kt; try by iDestruct "post" as "[_ post]".
iDestruct "post" as "[post _]".
by iApply ("post" $! (SignKey t)) => //;
rewrite [term_of_sign_key]unlock // !minted_TKey.
Qed.

Lemma wp_is_sign_key sk Ψ :
  minted sk -∗
  (∀ sk' : sign_key, ⌜sk = sk'⌝ -∗ Ψ #true) ∧ Ψ #false -∗
  WP is_sign_key sk {{ Ψ }}.
Proof.
by iIntros "H1 H2"; iApply twp_wp;
iApply (twp_is_sign_key with "H1 H2").
Qed.

End Proofs.

Arguments channel {Σ _ _} c.
