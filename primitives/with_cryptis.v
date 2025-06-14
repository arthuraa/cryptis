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

Definition mkchannel : val := λ: <>,
  let: "c" := ref []%V in
  let: "lock" := newlock #() in
  (put_chan "c" "lock", get_chan "c" "lock").

Definition send : val := λ: "c", Fst "c".
Definition recv : val := λ: "c", Snd "c" #().

Definition mknonce : val := λ: <>,
  let: "n" := ref #() in
  (#TNonce_tag, "n").

Definition mkakey : val := λ: <>,
  let: "n" := mknonce #() in
  tag (Tag $ nroot.@"keys".@"enc") "n".

Definition mksigkey : val := λ: <>,
  let: "n" := mknonce #() in
  tag (Tag $ nroot.@"keys".@"sig") "n".

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

Lemma wp_mkchannel Ψ :
  (∀ c, channel c -∗ Ψ c) ⊢
  WP mkchannel #() {{ Ψ }}.
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

Lemma twp_mknonce_gen (P Q : term → iProp Σ) E Ψ (Φ : term → iProp Σ) :
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
  WP mknonce #()%V @ E [{ Ψ }].
Proof.
rewrite /mknonce; iIntros "mint post".
wp_pures; wp_bind (ref _)%E; iApply twp_alloc=> //.
iIntros (a) "[_ token]".
iPoseProof (nonce_alloc P Q with "token") as "fresh".
iPoseProof ("mint" with "fresh") as ">(#? & #? & #? & ?)".
iSpecialize ("post" $! (TNonce a)).
wp_pures. rewrite val_of_term_unseal /=.
iApply ("post" with "[] [] [] [$]"); eauto.
Qed.

Lemma wp_mknonce_gen (P Q : term → iProp Σ) E Ψ (Φ : term → iProp Σ) :
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
  WP mknonce #()%V @ E {{ Ψ }}.
Proof.
iIntros "H1 H2". iApply twp_wp.
iApply (twp_mknonce_gen with "H1 H2").
Qed.

Lemma twp_mknonce_freshN (T : gset term) (P Q : term → iProp Σ) (T' : term → gset term) Ψ :
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
  WP mknonce #()%V [{ Ψ }].
Proof.
iIntros "#ctx minted_T #minted_T' post".
iApply (twp_mknonce_gen P Q ⊤ _
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

Lemma wp_mknonce_freshN (T : gset term) P Q (T' : term → gset term) Ψ :
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
  WP mknonce #()%V {{ Ψ }}.
Proof.
iIntros "#ctx H1 H2 H3".
by iApply twp_wp; iApply (twp_mknonce_freshN with "[//] H1 H2 H3").
Qed.

Lemma twp_mknonce_fresh (T : gset term) (P Q : term → iProp Σ) Ψ :
  cryptis_ctx -∗
  (∀ t, ⌜t ∈ T⌝ -∗ minted t) -∗
  (∀ t, ⌜∀ t', t' ∈ T → ¬ subterm t t'⌝ -∗
        ⌜is_nonce t⌝ -∗
        minted t -∗
        □ (public t ↔ ▷ □ P t) -∗
        □ (∀ t', dh_pred t t' ↔ ▷ □ Q t') -∗
        term_token t ⊤ -∗
        Ψ t) -∗
  WP mknonce #()%V [{ Ψ }].
Proof.
iIntros "#ctx minted_T post".
iApply (twp_mknonce_freshN T P Q (λ t : term, {[t]}) _
         with "[//] minted_T [] [post]") => //.
{ iIntros "%t". rewrite big_sepS_singleton. iModIntro.
  iSplit; by iIntros "?". }
iIntros "% ? ? ? ? ?".
rewrite big_sepS_singleton.
by iApply ("post" with "[$] [$] [$] [$] [$]").
Qed.

Lemma wp_mknonce_fresh (T : gset term) P Q Ψ :
  cryptis_ctx -∗
  (∀ t, ⌜t ∈ T⌝ -∗ minted t) -∗
  (∀ t, ⌜∀ t', t' ∈ T → ¬ subterm t t'⌝ -∗
        ⌜is_nonce t⌝ -∗
        minted t -∗
        □ (public t ↔ ▷ □ P t) -∗
        □ (∀ t', dh_pred t t' ↔ ▷ □ Q t') -∗
        term_token t ⊤ -∗
        Ψ t) -∗
  WP mknonce #()%V {{ Ψ }}.
Proof.
iIntros "#ctx H1 H2".
by iApply twp_wp; iApply (twp_mknonce_fresh with "[//] H1 H2").
Qed.

Lemma twp_mknonce (P Q : term → iProp Σ) Ψ :
  cryptis_ctx -∗
  (∀ t, ⌜is_nonce t⌝ -∗
        minted t -∗
        □ (public t ↔ ▷ □ P t) -∗
        □ (∀ t', dh_pred t t' ↔ ▷ □ Q t') -∗
        term_token t ⊤ -∗
        Ψ t) -∗
  WP mknonce #()%V [{ Ψ }].
Proof.
iIntros "#ctx post". iApply (twp_mknonce_fresh ∅ P Q) => //.
- iIntros "%". rewrite elem_of_empty. iDestruct 1 as "[]".
- iIntros "% _". iApply "post".
Qed.

Lemma wp_mknonce (P Q : term → iProp Σ) Ψ :
  cryptis_ctx -∗
  (∀ t, ⌜is_nonce t⌝ -∗
        minted t -∗
        □ (public t ↔ ▷ □ P t) -∗
        □ (∀ t', dh_pred t t' ↔ ▷ □ Q t') -∗
        term_token t ⊤ -∗
        Ψ t) -∗
  WP mknonce #()%V {{ Ψ }}.
Proof.
iIntros "#ctx H".
by iApply twp_wp; iApply (twp_mknonce with "[//] H").
Qed.

Lemma twp_mkakey Ψ :
  cryptis_ctx -∗
  (∀ t, public (TKey Seal t) -∗
        aenc_key t -∗
        secret t -∗
        term_token t ⊤ -∗
        Ψ t) -∗
  WP mkakey #() [{ Ψ }].
Proof.
iIntros "#ctx post". iMod unknown_alloc as (γ) "unknown".
rewrite /mkakey. wp_pures.
wp_bind (mknonce _).
iApply (twp_mknonce_freshN ∅ (λ _, known γ 1) (λ _, False%I)
  (λ t, {[Spec.tag (Tag $ nroot.@"keys".@"enc") t]})) => //.
- iIntros "% ?". by rewrite elem_of_empty.
- iIntros "%t". rewrite big_sepS_singleton minted_tag.
  iModIntro. by iSplit; iIntros "?".
iIntros "%t %fresh % #s_t #p_t _ token".
rewrite big_sepS_singleton.
pose (t' := Spec.tag (Tag $ nroot.@"keys".@"enc") t).
iAssert (secret t') with "[unknown]" as "tP"; first do 2?iSplit.
- iMod (known_alloc with "unknown") as "#known".
  iSpecialize ("p_t" with "known").
  iModIntro. by rewrite public_tag.
- iMod (known_alloc 2 with "unknown") as "#known".
  rewrite public_tag.
  iIntros "!> !>". iSplit.
  + iIntros "#contra".
    iPoseProof ("p_t" with "contra") as ">#known'".
    by iPoseProof (known_agree with "known known'") as "%".
  + iIntros "#contra".
    iApply "p_t". by iDestruct "contra" as ">[]".
- iIntros "#contra".
  rewrite public_tag.
  iPoseProof ("p_t" with "contra") as ">#known".
  by iPoseProof (unknown_known with "[$] [//]") as "[]".
iAssert (minted (TKey Open t')) as "s_t'".
  by rewrite minted_TKey minted_tag.
wp_pures. wp_bind (tag _ _). iApply twp_tag.
iAssert (public (TKey Seal t')) as "#?".
  iApply (public_enc_key with "ctx"). by eauto.
iApply ("post" with "[] [] [$] [$]") => //.
iSplit => //. iModIntro. rewrite public_tag.
iApply (bi.iff_trans _ (minted t ∧ ◇ (⌜Open = Seal⌝ ∨ public t))).
iSplit; first by iApply public_enc_key. iSplit.
- by iIntros "(_ & > [%|?])".
- iIntros "#?". iSplit => //. by iRight.
Qed.

Lemma wp_mkakey Ψ :
  cryptis_ctx -∗
  (∀ t, public (TKey Seal t) -∗
        aenc_key t -∗
        secret t -∗
        term_token t ⊤ -∗
        Ψ t) -∗
  WP mkakey #() {{ Ψ }}.
Proof.
iIntros "#? ?". iApply twp_wp. by wp_apply twp_mkakey.
Qed.

Lemma twp_mksigkey Ψ :
  cryptis_ctx -∗
  (∀ t, public (TKey Open t) -∗
        sign_key t -∗
        secret t -∗
        term_token t ⊤ -∗
        Ψ t) -∗
  WP mksigkey #() [{ Ψ }].
Proof.
iIntros "#ctx post". iMod unknown_alloc as (γ) "unknown".
rewrite /mksigkey. wp_pures.
wp_bind (mknonce _).
iApply (twp_mknonce_freshN ∅ (λ _, known γ 1) (λ _, False%I)
  (λ t, {[Spec.tag (Tag $ nroot.@"keys".@"sig") t]})) => //.
- iIntros "% ?". by rewrite elem_of_empty.
- iIntros "%t". rewrite big_sepS_singleton minted_tag.
  iModIntro. by iSplit; iIntros "?".
iIntros "%t %fresh % #s_t #p_t _ token".
rewrite big_sepS_singleton.
pose (t' := Spec.tag (Tag $ nroot.@"keys".@"sig") t).
iAssert (secret t') with "[unknown]" as "tP"; first do 2?iSplit.
- iMod (known_alloc with "unknown") as "#known".
  iSpecialize ("p_t" with "known").
  iModIntro. by rewrite public_tag.
- iMod (known_alloc 2 with "unknown") as "#known".
  rewrite public_tag.
  iIntros "!> !>". iSplit.
  + iIntros "#contra".
    iPoseProof ("p_t" with "contra") as ">#known'".
    by iPoseProof (known_agree with "known known'") as "%".
  + iIntros "#contra".
    iApply "p_t". by iDestruct "contra" as ">[]".
- iIntros "#contra".
  rewrite public_tag.
  iPoseProof ("p_t" with "contra") as ">#known".
  by iPoseProof (unknown_known with "[$] [//]") as "[]".
iAssert (minted t') as "s_t'"; first by rewrite minted_tag.
wp_pures. wp_bind (tag _ _). iApply twp_tag.
iAssert (public (TKey Open t')) as "#?".
  iApply (public_sig_key with "ctx"). by eauto.
iApply ("post" with "[] [] [$] [$]") => //.
iSplit => //. iModIntro. rewrite public_tag.
iApply (bi.iff_trans _ (minted t ∧ ◇ (⌜Seal = Open⌝ ∨ public t))).
iSplit; first by iApply public_sig_key.
iSplit.
- by iIntros "(_ & > [%|?])".
- iIntros "#?". iSplit => //. by iRight.
Qed.

Lemma wp_mksigkey Ψ :
  cryptis_ctx -∗
  (∀ t, public (TKey Open t) -∗
        sign_key t -∗
        secret t -∗
        term_token t ⊤ -∗
        Ψ t) -∗
  WP mksigkey #() {{ Ψ }}.
Proof.
iIntros "#? ?". iApply twp_wp. by wp_apply twp_mksigkey.
Qed.

End Proofs.

Arguments channel {Σ _ _} c.
