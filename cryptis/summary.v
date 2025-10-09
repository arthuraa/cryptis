(**

This file consolidates all the claims made in the paper.

*)


From mathcomp Require Import ssreflect.
From stdpp Require Import list.
From iris.base_logic Require Import base_logic iprop.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import adequacy.
From iris.heap_lang Require Import adequacy notation proofmode.
From cryptis Require Import lib cryptis primitives adequacy role.

(** Equational properties of Diffie-Hellman terms.

[TExpN] takes in a base and a list of exponents and constructs a Diffie-Hellman
term.

*)

Check TExpN : term → list term → term.

(** Exponents can be regrouped and permuted *)
Lemma TExpNA t ts1 ts2 : TExpN (TExpN t ts1) ts2 = TExpN t (ts1 ++ ts2).
Proof. exact: TExpNA. Qed.

Lemma TExpN_perm t ts1 ts2 : ts1 ≡ₚ ts2 → TExpN t ts1 = TExpN t ts2.
Proof. by move=> ->. Qed.

Lemma TExpNC t ts1 ts2 : TExpN t (ts1 ++ ts2) = TExpN t (ts2 ++ ts1).
Proof. exact: TExpNC. Qed.

Lemma TExpN0 t : TExpN t [] = t.
Proof. exact: TExpN0. Qed.

Section Specifications.

Context `{!heapGS Σ, !cryptisGS Σ}.

Implicit Types (t : term) (v : val).

(** [public t] means that the term [t] can be sent over the network. *)

Check public : term → iProp Σ.

Lemma public_persistent t : Persistent (public t).
Proof. apply _. Qed.

Lemma public_TInt n : public (TInt n) ⊣⊢ True.
Proof. exact: public_TInt. Qed.

Lemma public_TPair t1 t2 : public (TPair t1 t2) ⊣⊢ public t1 ∧ public t2.
Proof. exact: public_TPair. Qed.

Lemma public_TKey kt t :
  public (TKey kt t) ⊣⊢ public t ∨ minted t ∧ ⌜Spec.public_key_type kt⌝.
Proof. exact: public_TKey. Qed.

Lemma public_TSeal k N t :
  public (TSeal k (Spec.tag (Tag N) t)) ⊣⊢
  public k ∧ public t
  ∨ minted k ∧ minted t
    ∧ match func_of_term k with
      | Some F => ∃ φ,
          ⌜Spec.is_seal_key k⌝
          ∧ seal_pred F N φ
          ∧ □ ▷ φ (Spec.skey k) t
          ∧ match Spec.open_key k with
            | Some k' => □ (public k' → public t)
            | None => True
            end
      | None => True
      end.
Proof.
rewrite public_TSeal.
apply bi.or_proper; first by rewrite public_tag.
rewrite !minted_TSeal minted_tag assoc.
apply bi.and_proper => //.
case: func_of_term => // F.
rewrite -bi.and_exist_l. apply bi.and_proper => //.
iSplit.
- iIntros "[H1 H2]".
  iDestruct "H1" as "(% & % & % & %e_t & #? & #?)".
  case/Spec.tag_inj: e_t=> /Tag_inj <- <-.
  iExists _. iSplit => //. iSplit => //.
  case: Spec.open_key => // ?.
  by rewrite public_tag.
- iIntros "(%φ & #? & #? & #?)".
  iSplit.
  + by iExists _, _, _; eauto.
  + case: Spec.open_key => // ?. by rewrite public_tag.
Qed.

Definition dh_key t : iProp Σ :=
  □ (∀ t', dh_pred t t' ↔ ▷ ⌜length (exps t') = 1⌝).

Lemma public_TExpN1 t1 t2 :
  ¬ is_exp t1 →
  dh_key t2 -∗
  minted t1 -∗
  minted t2 -∗
  public (TExpN t1 [t2]).
Proof.
iIntros "%exp_t1 #dh #m1 #m2".
rewrite public_TExp_iff //.
iRight. do !iSplit => //. iApply "dh".
by rewrite exps_TExpN exps_expN.
Qed.

Lemma public_TExpN t ts :
  ¬ is_exp t →
  ts ≠ [] →
  minted t -∗
  ([∗ list] t' ∈ ts, minted t' ∧ dh_key t') -∗
  public (TExpN t ts) ↔
  (∃ t' ts', ⌜ts ≡ₚ t' :: ts'⌝ ∧ public (TExpN t ts') ∧ public t') ∨
  ▷ ⌜length ts = 1⌝.
Proof.
iIntros "%exp_t %ts_n0 #m_t #ts".
rewrite public_TExpN //.
iSplit; iIntros "[#?|H]"; eauto; iRight.
- iDestruct "H" as "[_ H]".
  case: ts ts_n0 => // t' ts _ /=.
  iDestruct "ts" as "[[_ ts] _]".
  iDestruct "H" as "[H _]".
  iSpecialize ("ts" with "H").
  by rewrite exps_TExpN // exps_expN.
- iSplit.
  + iApply minted_TExpN. iSplit => //.
    rewrite !big_sepL_forall. iIntros "% % H'".
    by iDestruct ("ts" with "H'") as "[??]".
  + rewrite !big_sepL_forall. iIntros "% % H'".
    iDestruct ("ts" with "H'") as "[? H']".
    iApply "H'". by rewrite exps_TExpN exps_expN //.
Qed.

Lemma seal_pred_agree F N φ₁ φ₂ :
  seal_pred F N φ₁ -∗
  seal_pred F N φ₂ -∗
  ▷ ∀ k t, φ₁ k t ≡ φ₂ k t.
Proof.
iIntros "#pred1 #pred2 %k %t".
by iApply seal_pred_agree.
Qed.

Lemma seal_pred_set F N E φ :
  ↑N ⊆ E →
  seal_pred_token F E ==∗ seal_pred F N φ.
Proof.
iIntros "%sub token".
iMod (seal_pred_set with "token") as "[??]"; eauto.
Qed.

Lemma seal_pred_token_difference F E1 E2 :
  E1 ⊆ E2 →
  seal_pred_token F E2 ⊣⊢ seal_pred_token F E1 ∗ seal_pred_token F (E2 ∖ E1).
Proof. exact: seal_pred_token_difference. Qed.

Lemma term_meta_persistent `{Countable L} t N (x : L) :
  Persistent (term_meta t N x).
Proof. apply _. Qed.

Lemma term_meta_agree `{Countable L} t N (x1 x2 : L) :
  term_meta t N x1 -∗
  term_meta t N x2 -∗
  ⌜x1 = x2⌝.
Proof. exact: term_meta_agree. Qed.

Lemma term_meta_set `{Countable L} t N E (x : L) :
  ↑N ⊆ E →
  term_token t E ==∗ term_meta t N x.
Proof. exact: term_meta_set. Qed.

Lemma term_meta_token `{Countable L} t N E (x : L) :
  ↑N ⊆ E →
  term_meta t N x -∗ term_token t E -∗ False.
Proof.
iIntros "% #meta token".
by iApply (term_meta_token with "token meta").
Qed.

Lemma term_token_difference t E1 E2 :
  E1 ⊆ E2 →
  term_token t E2 ⊣⊢ term_token t E1 ∗ term_token t (E2 ∖ E1).
Proof. exact: term_token_difference. Qed.

Lemma wp_send c t :
  channel c -∗
  ▷ public t -∗
  WP send c t {{ v, ⌜v = #()⌝ }}.
Proof.
iIntros "#c #p".
by wp_apply (wp_send with "c p").
Qed.

Lemma wp_recv c :
  channel c -∗
  WP recv c {{ v, ∃ t, ⌜v = t⌝ ∗ public t }}.
Proof.
iIntros "#c".
wp_apply (wp_recv with "c"). by eauto.
Qed.

Lemma wp_mk_nonce P T :
  cryptis_ctx -∗
  □ (∀ t t', ⌜t' ∈ T t⌝ -∗ ⌜subterm t t'⌝ ∧ (minted t → minted t')) -∗
  WP mk_nonce #()
    {{ v, ∃ t, ⌜v = t⌝ ∗
          minted t ∗ □ (public t ↔ ▷ □ P t) ∗ dh_key t ∗
          [∗ set] t' ∈ T t, term_token t' ⊤ }}.
Proof.
iIntros "#ctx #T".
wp_apply (wp_mk_nonce_freshN ∅ P (λ t', ⌜length (exps t') = 1⌝)%I T) => //.
- iIntros "% %"; set_solver.
- iIntros "%t". rewrite big_sepS_forall.
  iIntros "%t' %t_t' !>".
  iDestruct ("T" $! t t' with "[//]") as "[% ?]".
  iSplit; eauto. iIntros "#m_t'". by iApply (subterm_minted with "m_t'").
iIntros "%t _ _ #m_t #s_t #dh_t tok".
iExists _. iFrame. do !iSplit => //.
iIntros "!> %t'".
iSpecialize ("dh_t" $! t').
by rewrite bi.intuitionistic_intuitionistically.
Qed.

Lemma unknown_alloc : ⊢ |==> ∃ γ, unknown γ.
Proof. exact: unknown_alloc. Qed.

Lemma secret_alloc t γ :
  □ (public t ↔ ▷ known γ 1) -∗
  unknown γ -∗
  secret t.
Proof. exact: secret_alloc. Qed.

Lemma secret_public t : secret t ==∗ public t.
Proof. exact: secret_public. Qed.

Lemma secret_not_public t : secret t -∗ public t -∗ ▷ False.
Proof. exact: secret_not_public. Qed.

Lemma freeze_secret t : secret t ==∗ □ (public t ↔ ▷ False).
Proof. exact: freeze_secret. Qed.

Lemma wp_aenc (sk : aenc_key) N t φ :
  aenc_pred N φ -∗
  minted sk -∗
  minted t -∗
  (public t ∨ □ φ sk t ∧ □ (public sk → public t)) -∗
  WP aenc (Spec.pkey sk) (Tag N) t
    {{ v, ∃ t', ⌜v = t'⌝ ∗ public t' }}.
Proof.
iIntros "#? #? #? #?".
iApply (wp_aenc with "[//] [//] [//] [//]").
iIntros "%m #p_m". by eauto.
Qed.

Lemma wp_adec (sk : aenc_key) N t φ :
  aenc_pred N φ -∗
  public t -∗
  WP adec sk (Tag N) t
    {{ v, ⌜v = NONEV⌝
          ∨ (∃ t', ⌜v = SOMEV t'⌝ ∧ minted t' ∧
                 (public t' ∨ □ φ sk t' ∧ □ (public sk → public t'))) }}.
Proof.
iIntros "#? #?".
iApply (wp_adec with "[//] [//]"). iSplit; eauto.
iIntros "% #? #?". iRight. eauto.
Qed.

Lemma wp_sign (sk : sign_key) N t φ :
  sign_pred N φ -∗
  minted sk -∗
  public t -∗
  public sk ∨ □ φ sk t -∗
  WP sign sk (Tag N) t {{ v, ∃ t', ⌜v = t'⌝ ∗ public t' }}.
Proof.
iIntros "#? #? #? #?".
wp_apply wp_sign; eauto.
Qed.

Lemma wp_verify (sk : sign_key) N t φ :
  sign_pred N φ -∗
  public t -∗
  WP verify (Spec.pkey sk) (Tag N) t
    {{ v, ⌜v = NONEV⌝ ∨
          (∃ t', ⌜v = SOMEV t'⌝ ∗ public t' ∧ (public sk ∨ □ φ sk t')) }}.
Proof.
iIntros "#? #?".
wp_apply wp_verify; eauto. iSplit; eauto.
iIntros "% #? #?". iRight; eauto.
Qed.

Lemma wp_senc (sk : senc_key) N t φ :
  senc_pred N φ -∗
  minted sk -∗
  minted t -∗
  public sk ∨ □ φ sk t -∗
  □ (public sk → public t) -∗
  WP senc sk (Tag N) t {{ v, ∃ t', ⌜v = t'⌝ ∗ public t' }}.
Proof.
iIntros "#? #? #? #? #?". wp_apply wp_senc; eauto. 
Qed.

Lemma wp_sdec (sk : senc_key) N t φ :
  senc_pred N φ -∗
  public t -∗
  WP sdec sk (Tag N) t
    {{ v, ⌜v = NONEV⌝ ∨
          (∃ t', ⌜v = SOMEV t'⌝ ∗ minted t' ∗
                 (public sk ∨ □ φ sk t') ∗
                 □ (public sk → public t')) }}.
Proof.
iIntros "#? #?". wp_apply wp_sdec; eauto.
iSplit; eauto. iIntros "% #? #? #?". iRight. eauto.
Qed.

Lemma wp_mk_aenc_key :
  cryptis_ctx -∗
  WP mk_aenc_key #() {{ v,
    ∃ sk : aenc_key, ⌜v = sk⌝ ∗
      minted sk ∗ secret sk ∗ term_token sk ⊤
  }}.
Proof.
iIntros "#ctx". iApply wp_mk_aenc_key => //.
iIntros "%sk #? ? ?". iFrame. by eauto.
Qed.

Lemma wp_mk_sign_key :
  cryptis_ctx -∗
  WP mk_sign_key #() {{ v,
    ∃ sk : sign_key, ⌜v = sk⌝ ∗
      minted sk ∗ secret sk ∗ term_token sk ⊤
  }}.
Proof.
iIntros "#ctx". iApply wp_mk_sign_key => //.
iIntros "%sk #? ? ?". iFrame. by eauto.
Qed.

Lemma wp_mk_senc_key :
  cryptis_ctx -∗
  WP mk_senc_key #() {{ v,
    ∃ sk : senc_key, ⌜v = sk⌝ ∗
      minted sk ∗ secret sk ∗ term_token sk ⊤
  }}.
Proof.
iIntros "#ctx". iApply wp_mk_senc_key => //.
iIntros "%sk #? ? ?". iFrame. by eauto.
Qed.

Lemma wp_init_network :
  cryptis_ctx -∗
  WP init_network #() {{ c, channel c }}.
Proof.
iIntros "#ctx". wp_apply wp_init_network; eauto.
Qed.

End Specifications.

Lemma cryptis_adequacy `{heapGpreS Σ, cryptisGpreS Σ} (f : val) σ φ :
  (∀ `{heapGS Σ} `{cryptisGS Σ} (c : val),
      cryptis_ctx -∗ channel c -∗
      seal_pred_token AENC ⊤ -∗
      seal_pred_token SIGN ⊤ -∗
      seal_pred_token SENC ⊤ -∗
      WP f c {{ v, ⌜φ v⌝ }}) →
  adequate NotStuck (run_network f) σ (λ v _, φ v).
Proof.
move=> wp; apply: cryptis_adequacy.
iIntros (???) "#? #? (? & ? & ? & _)".
wp_apply (wp with "[//] [//] [$] [$] [$]").
Qed.
