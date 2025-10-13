(**

This file consolidates the main results of the paper and checks that the
security proofs of the main case studies are free of axioms and admitted lemmas.
For more details on thr proofs of individual case studies, check the
corresponding directories under examples/.

*)


From mathcomp Require Import ssreflect.
From stdpp Require Import list.
From iris.base_logic Require Import base_logic iprop.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import adequacy.
From iris.heap_lang Require Import adequacy notation proofmode.
From cryptis Require Import lib cryptis primitives adequacy role.
From cryptis.lib Require Import replica.
From cryptis.examples Require iso_dh conn rpc store.
From cryptis.examples.nsl    Require impl proofs game.
From cryptis.examples.iso_dh Require game.
From cryptis.examples.store  Require db game.

Section Section_2_CoreLogic.


(**

* Equational properties of Diffie-Hellman terms: exponents can be regrouped and
permuted.

*)

Lemma TExpNA t ts1 ts2 : TExpN (TExpN t ts1) ts2 = TExpN t (ts1 ++ ts2).
Proof. exact: TExpNA. Qed.

Lemma TExpN_perm t ts1 ts2 : ts1 ≡ₚ ts2 → TExpN t ts1 = TExpN t ts2.
Proof. by move=> ->. Qed.

Lemma TExpNC t ts1 ts2 : TExpN t (ts1 ++ ts2) = TExpN t (ts2 ++ ts1).
Proof. exact: TExpNC. Qed.

Lemma TExpN0 t : TExpN t [] = t.
Proof. exact: TExpN0. Qed.

Section WithCryptis.

Context `{!heapGS Σ, !cryptisGS Σ}.

Implicit Types (t : term) (v : val).

(**

* Definition of public terms.

*)

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

Lemma public_TExpN2 t t1 t2 :
  ¬ is_exp t →
  minted t -∗
  minted t1 -∗
  minted t2 -∗
  dh_key t1 -∗
  dh_key t2 -∗
  public (TExpN t [t1; t2]) ↔ ◇ (public t1 ∨ public t2).
Proof.
iIntros "% #m_t #m1 #m2 #dh1 #dh2".
rewrite public_TExp2_iff //.
iSplit.
- iIntros "#[[??]|[[??]|H]]"; eauto.
  iDestruct "H" as "(_ & H & _)".
  iPoseProof ("dh1" with "H") as ">%contra".
  rewrite exps_TExpN length_app /= in contra; lia.
- rewrite /bi_except_0. iIntros "#[H|[H|H]]".
  + iRight. iRight. rewrite minted_TExpN /=.
    iSplit; eauto. iSplit.
    * iApply "dh1". by iDestruct "H" as ">[]".
    * iApply "dh2". by iDestruct "H" as ">[]".
  + iRight. iLeft. iSplit => //.
    iApply public_TExpN1 => //.
  + iLeft. iSplit => //.
    iApply public_TExpN1 => //.
Qed.

(**

* Specifications of core programming primitives: network and nonce generation.

*)

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

(**

* Properties of sealing predicates and their tokens.

*)

Lemma seal_pred_persistent F N φ : Persistent (seal_pred F N φ).
Proof. apply _. Qed.

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

(**

* Properties of term metadata and its tokens.

*)

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

End WithCryptis.

(**

* Theorem 2.1

*)

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

End Section_2_CoreLogic.

Section Section_2_1_DerivedConstructs.

(**

* The [secret] predicate (Figure 2).

*)

Context `{!heapGS Σ, !cryptisGS Σ}.
Implicit Types (t : term) (v : val).

Lemma pending_alloc : ⊢ |==> ∃ γ, pending γ.
Proof. exact: pending_alloc. Qed.

Lemma shot_alloc γ n : pending γ ==∗ shot γ n.
Proof. exact: shot_alloc. Qed.

Lemma pending_shot γ n : pending γ -∗ shot γ n -∗ False.
Proof. exact: pending_shot. Qed.

Lemma shot_agree γ n m : shot γ n -∗ shot γ m -∗ ⌜n = m⌝.
Proof. exact: shot_agree. Qed.

Lemma secret_alloc t γ :
  □ (public t ↔ ▷ shot γ 1) -∗
  pending γ -∗
  secret t.
Proof. exact: secret_alloc. Qed.

Lemma secret_public t : secret t ==∗ public t.
Proof. exact: secret_public. Qed.

Lemma freeze_secret t : secret t ==∗ □ (public t ↔ ▷ False).
Proof. exact: freeze_secret. Qed.

Lemma secret_not_public t : secret t -∗ public t -∗ ▷ False.
Proof. exact: secret_not_public. Qed.

(**

* Derived specifications for asymmetric encryption (Figure 3)

*)

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

(**

* Derived specifications for digital signatures and symmetric encryption
  (omitted from paper)

*)

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

End Section_2_1_DerivedConstructs.

Section Section_3_KeyValueOverview.

Import iso_dh conn rpc store store.game.

Context `{!heapGS Σ, !cryptisGS Σ, !Conn.connGS Σ, !RPC.rpcGS Σ, !storeGS Σ}.

Implicit Types skI skR : sign_key.

(**

* Core specifications and rules

*)

Lemma wp_store_client_connect c skI skR :
  channel c ∗
  cryptis_ctx ∗
  store_ctx ∗
  minted skI ∗
  minted skR -∗
  {{{ db_disconnected skI skR }}}
    Client.connect c skI (Spec.pkey skR)
  {{{ cs, RET (repr cs);
      db_connected skI skR cs }}}.
Proof. exact: wp_client_connect. Qed.

Lemma wp_store_client_close skI skR cs :
  store_ctx -∗
  {{{ db_connected skI skR cs }}}
    Client.close (repr cs)
  {{{ RET #(); db_disconnected skI skR ∗ public (si_key cs) }}}.
Proof. exact: wp_client_close. Qed.

Lemma wp_store_client_load skI skR cs t1 t2 :
  cryptis_ctx ∗
  store_ctx ∗
  public t1 -∗
  {{{ db_connected skI skR cs ∗
      db_mapsto skI skR t1 t2 }}}
    Client.load (repr cs) t1
  {{{ t2', RET (repr t2');
      db_connected skI skR cs ∗
      db_mapsto skI skR t1 t2 ∗
      public t2' ∗
      (compromised Init cs ∨ ⌜t2' = t2⌝) }}}.
Proof. exact: wp_client_load. Qed.

Lemma wp_store_client_create skI skR cs t1 t2 :
  cryptis_ctx ∗
  store_ctx ∗
  public t1 ∗
  public t2 -∗
  {{{ db_connected skI skR cs ∗
      db_free_at skI skR {[t1]} }}}
    Client.create (repr cs) t1 t2
  {{{ RET #();
      db_connected skI skR cs ∗
      db_mapsto skI skR t1 t2 }}}.
Proof. exact: wp_client_create. Qed.

Lemma wp_store_client_store skI skR cs t1 t2 t2' :
  cryptis_ctx ∗
  store_ctx ∗
  public t1 ∗
  public t2' -∗
  {{{ db_connected skI skR cs ∗ db_mapsto skI skR t1 t2 }}}
    Client.store (repr cs) t1 t2'
  {{{ RET #(); db_connected skI skR cs ∗ db_mapsto skI skR t1 t2' }}}.
Proof. exact: wp_client_store. Qed.

Lemma db_mapsto_excl skI skR t t1 t2 :
  db_mapsto skI skR t t1 -∗
  db_mapsto skI skR t t2 -∗
  False.
Proof. exact: db_mapsto_excl. Qed.

Lemma db_connected_ok skI skR cs :
  secret skI -∗
  secret skR -∗
  db_connected skI skR cs -∗
  ▷ □ ¬ compromised Init cs.
Proof.
iIntros "sI sR conn".
by iMod (db_connected_ok with "conn sI sR") as "?".
Qed.

Lemma db_client_alloc skI skR :
  term_token skI (↑ (dbN.@"client".@(skR : term))) ==∗
  db_disconnected skI skR ∗ db_free_at skI skR ⊤.
Proof.
iIntros "token".
iMod (client_alloc with "token") as "(? & ? & ?)"; eauto.
by iFrame.
Qed.

Lemma db_free_at_diff skI skR T1 T2 :
  T1 ## T2 →
  db_free_at skI skR (T1 ∪ T2) ⊢
  db_free_at skI skR T1 ∗ db_free_at skI skR T2.
Proof.
move=> dis.
assert (T1 ⊆ T1 ∪ T2) as sub by set_solver.
assert (T2 = (T1 ∪ T2) ∖ T1) as e by set_solver.
by rewrite (db_free_at_diff _ _ sub) -e.
Qed.

(**

* Game security (for Figure 6)

*)

Lemma store_secure σ₁ σ₂ t₂ e₂ :
  rtc erased_step ([run_network store.game.game], σ₁) (t₂, σ₂) →
  e₂ ∈ t₂ →
  not_stuck e₂ σ₂.
Proof. exact: store_secure. Qed.

End Section_3_KeyValueOverview.

Section Section_4_NSL.

Context `{!heapGS Σ, !cryptisGS Σ}.

Implicit Types skI skR : aenc_key.

Import nsl.impl nsl.proofs nsl.game.

(**

* Security of initiator and responder (Theorem 4.1)

*)

Lemma wp_nsl_initiator c skI skR :
  channel c ∗
  cryptis_ctx ∗
  nsl_ctx ∗
  minted skI ∗
  minted skR -∗
  {{{ True }}}
    init c skI (Spec.pkey skR)
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨ ∃ si,
        ⌜r = Some (si_key si)⌝ ∗
        session_NSL skI skR si ∗
        term_token (si_init_share si) (⊤ ∖ ↑nslN) }}}.
Proof. exact: wp_init. Qed.

Lemma wp_nsl_responder c skR :
  channel c ∗
  cryptis_ctx ∗
  nsl_ctx ∗
  minted skR -∗
  {{{ True }}}
    resp c skR
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨ ∃ skI si,
        ⌜r = Some (Spec.pkey skI, si_key si)⌝ ∗
        session_NSL skI skR si ∗
        term_token (si_resp_share si) (⊤ ∖ ↑nslN)
  }}}.
Proof. exact: wp_resp. Qed.

(**

* Security of game (code in Figure 9)

*)

Lemma nsl_secure σ₁ σ₂ t₂ e₂ :
  rtc erased_step ([run_network nsl.game.game], σ₁) (t₂, σ₂) →
  e₂ ∈ t₂ →
  not_stuck e₂ σ₂.
Proof. exact: nsl_secure. Qed.

End Section_4_NSL.

Section Section_5_ISO.

Context `{!heapGS Σ, !cryptisGS Σ}.

Implicit Types skI skR : sign_key.

Import iso_dh iso_dh.game.

(**

* Simplified security result for ISO protocol (Theorem 5.1)

*)

Lemma wp_iso_initiator c skI skR :
  channel c ∗
  cryptis_ctx ∗
  iso_dh_ctx ∗
  minted skI ∗
  minted skR -∗
  {{{ True }}}
    initiator c skI (Spec.pkey skR)
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨ ∃ si,
        ⌜r = Some (si_key si)⌝ ∗
        session_weak skI skR si ∗
        term_token (si_init_share si) (⊤ ∖ ↑iso_dhN)
  }}}.
Proof. exact: wp_initiator_weak. Qed.

Lemma wp_iso_responder c skR :
  channel c ∗ cryptis_ctx ∗ iso_dh_ctx ∗ minted skR -∗
  {{{ True }}}
    responder c skR
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨ ∃ skI si,
        ⌜r = Some (Spec.pkey skI, si_key si)⌝ ∗
        session_weak skI skR si ∗
        term_token (si_resp_share si) (⊤ ∖ ↑iso_dhN) }}}.
Proof. exact: wp_responder_weak. Qed.


(**

* Security of ISO game (code in Figure 13)

*)

Lemma iso_secure σ₁ σ₂ t₂ e₂ :
  rtc erased_step ([run_network iso_dh.game.game], σ₁) (t₂, σ₂) →
  e₂ ∈ t₂ →
  not_stuck e₂ σ₂.
Proof. exact: iso_dh_secure. Qed.

(**

* Properties of session compromise (Figure 14)

*)

Lemma release_token_released t :
  release_token t -∗ released t -∗ False.
Proof.
iIntros "token #meta". by iApply (term_meta_token with "meta token").
Qed.

Lemma release t : release_token t ==∗ released t.
Proof. exact: release. Qed.

Lemma compromised_public rl si : compromised rl si ⊢ public (si_key si).
Proof. exact: compromised_public. Qed.

Lemma session_compromised' skI skR rl si :
  session skI skR rl si -∗
  compromised rl si -∗
  public skI ∨ public skR.
Proof. exact: session_compromised'. Qed.

Lemma session_not_compromised skI skR rl si :
  session skI skR rl si -∗
  secret skI -∗
  secret skR -∗
  ▷ □ ¬ compromised rl si.
Proof.
iIntros "H1 H2 H3".
by iMod (session_not_compromised with "H1 H2 H3").
Qed.

Lemma session_released skI skR rl si :
  session skI skR rl si -∗
  ▷ released (si_init_share si) -∗
  ▷ released (si_resp_share si) -∗
  public (si_key si).
Proof.
iIntros "#sess #r1 #r2".
iApply session_released_session => //.
by iSplit.
Qed.

Lemma session_compromised skI skR rl si :
  session skI skR rl si -∗
  public (si_key si) -∗
  release_token (si_share_of rl si) -∗
  ▷ compromised rl si.
Proof.
iIntros "H1 H2 H3". by iMod (session_compromised with "H1 H2 H3").
Qed.

(**

* Stronger specifications for ISO protocol (the initiator's is in Theorem 5.2;
  the responder's is omitted in the paper).

*)

Lemma wp_iso_initiator_strong (failed : bool) c skI skR :
  channel c ∗
  cryptis_ctx ∗
  iso_dh_ctx ∗
  minted skI ∗
  minted skR ∗
  (if failed then public skI ∨ public skR else True) -∗
  {{{ True }}}
    initiator c skI (Spec.pkey skR)
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨ ∃ si,
        ⌜r = Some (si_key si)⌝ ∗
        session skI skR Init si ∗
        □ (⌜failed⌝ → compromised Init si) ∗
        release_token (si_init_share si) ∗
        term_token (si_init_share si) (⊤ ∖ ↑iso_dhN)
  }}}.
Proof. exact: wp_initiator. Qed.

Lemma wp_iso_responder_confirm_strong (failed : bool) c skI skR ga :
  {{{ channel c ∗ cryptis_ctx ∗ iso_dh_ctx ∗
      public ga ∗ minted skI ∗ minted skR ∗
      if failed then public skI ∨ public skR
      else True }}}
    responder_confirm c skR ga (Spec.pkey skI)
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨ ∃ si,
        ⌜r = Some (si_key si)⌝ ∗
        session skI skR Resp si ∗
        □ (⌜failed⌝ → compromised Resp si) ∗
        release_token (si_resp_share si) ∗
        term_token (si_resp_share si) (⊤ ∖ ↑iso_dhN) }}}.
Proof. exact: wp_responder_confirm. Qed.

End Section_5_ISO.

Section Section_6_ReliableConnections.

Import iso_dh conn.

Context `{!heapGS Σ, !cryptisGS Σ, !Conn.connGS Σ}.

Implicit Types skI skR : sign_key.

(**

* Specifications of Figure 15.

*)

Lemma wp_conn_connect P c skI skR :
  channel c ∗
  cryptis_ctx ∗
  iso_dh_ctx ∗
  minted skI ∗
  minted skR -∗
  {{{ (public skI ∨ public skR) ∨ P }}}
    Conn.connect c skI (Spec.pkey skR)
  {{{ cs, RET (repr cs);
      Conn.connected skI skR Init cs ∗
      (compromised Init cs ∨ P) ∗
      release_token (si_init_share cs) ∗
      term_token (si_init_share cs) (⊤ ∖ ↑iso_dhN ∖ ↑Conn.connN) }}}.
Proof. exact: Conn.wp_connect. Qed.

Lemma wp_conn_confirm P c skI skR ga :
  channel c ∗
  cryptis_ctx ∗
  iso_dh_ctx ∗
  public ga ∗
  minted skI ∗
  minted skR -∗
  {{{ (public skI ∨ public skR) ∨ P }}}
    Conn.confirm c skR (ga, Spec.pkey skI)%V
  {{{ cs, RET (repr cs);
      Conn.connected skI skR Resp cs ∗
      (compromised Resp cs ∨ P) ∗
      release_token (si_resp_share cs) ∗
      term_token (si_resp_share cs) (⊤ ∖ ↑iso_dhN ∖ ↑Conn.connN) }}}.
Proof. exact: Conn.wp_confirm. Qed.

Lemma wp_conn_send skI skR rl cs N ts φ :
  senc_pred N (Conn.conn_pred rl φ) ∗
  ([∗ list] t ∈ ts, public t) -∗
  {{{ Conn.connected skI skR rl cs ∗
      (public (si_key cs) ∨ φ skI skR cs ts) }}}
    Conn.send (repr cs) (Tag N) (repr ts)
  {{{ RET #(); Conn.connected skI skR rl cs }}}.
Proof. exact: Conn.wp_send. Qed.

Lemma wp_conn_recv N skI skR rl cs φ :
  senc_pred N (Conn.conn_pred (swap_role rl) φ) -∗
  {{{ Conn.connected skI skR rl cs }}}
    Conn.recv (repr cs) (Tag N)
  {{{ ts, RET (repr (ts : list term));
      Conn.connected skI skR rl cs ∗
      ([∗ list] t ∈ ts, public t) ∗
      (public (si_key cs) ∨ φ skI skR cs ts) }}}.
Proof. exact: Conn.wp_recv. Qed.

End Section_6_ReliableConnections.

Section Section_7_RemoteProcedureCalls.

Import iso_dh conn rpc.

Context `{!heapGS Σ, !cryptisGS Σ, !Conn.connGS Σ, !RPC.rpcGS Σ}.

Implicit Types skI skR : sign_key.

(**

* Specifications of Figure 17

*)

Lemma wp_rpc_call N φ ψ skI skR cs (ts : list term) :
  cryptis_ctx ∗
  RPC.ctx ∗
  ([∗ list] t ∈ ts, public t) ∗
  RPC.rpc N φ ψ -∗
  {{{ RPC.client_connected skI skR cs ∗
      (compromised Init cs ∨ φ skI skR cs ts) }}}
    RPC.call (repr cs) (Tag N) (repr ts)
  {{{ ts', RET (repr ts');
      RPC.client_connected skI skR cs ∗
      (compromised Init cs ∨ ψ skI skR cs ts ts') ∗
      ([∗ list] t ∈ ts', public t) }}}.
Proof. exact: RPC.wp_call. Qed.

Lemma wp_rpc_close skI skR cs :
  RPC.ctx -∗
  {{{ RPC.client_connected skI skR cs }}}
    RPC.close (repr cs)
  {{{ RET #(); public (si_key cs) }}}.
Proof. exact: RPC.wp_close. Qed.

End Section_7_RemoteProcedureCalls.

Section Section_8_KeyValueStore.

(**

* Properties of db_state (Figure 18)

NB: The DbStateAgree rule in the paper was stated both for allocated and free
keys.  In our development, there is a separate [db_state_create] lemma for
reasoning about free keys.

*)

Section DBStateResources.

Import db.

Context `{!heapGS Σ, !cryptisGS Σ, !dbGS Σ}.

Implicit Types skI skR : sign_key.

Lemma db_state_alloc kI kR N :
  term_token kI (↑N.@"client".@kR.@"state") ==∗
  DB.db_state kI kR N ∅ ∗
  DB.free_at kI kR N ⊤.
Proof.
iIntros "token".
iMod (DB.db_state_alloc with "token") as "(?&?&?)"; eauto.
by iFrame.
Qed.

Lemma db_state_agree kI kR N db t1 t2 :
  DB.db_state kI kR N db -∗
  DB.mapsto kI kR N t1 t2 -∗
  ⌜db !! t1 = Some t2⌝.
Proof. exact: DB.db_state_mapsto. Qed.

Lemma db_state_update t2' kI kR N db t1 t2 :
  DB.db_state kI kR N db -∗
  DB.mapsto kI kR N t1 t2 ==∗
  DB.db_state kI kR N (<[t1 := t2']>db) ∗
  DB.mapsto kI kR N t1 t2'.
Proof. exact: DB.db_state_update. Qed.

Lemma db_state_create t1 t2 kI kR N db :
  DB.db_state kI kR N db -∗
  DB.free_at kI kR N {[t1]} ==∗
  ⌜db !! t1 = None⌝ ∗
  DB.db_state kI kR N (<[t1 := t2]>db) ∗
  DB.mapsto kI kR N t1 t2.
Proof. exact: DB.db_state_create. Qed.

End DBStateResources.

(**

* Properties of db_main and related predicates (rest of Figure 18)

*)

Section DbMainResources.

Import iso_dh conn rpc store store.game.

Context `{!heapGS Σ, !cryptisGS Σ, !Conn.connGS Σ, !RPC.rpcGS Σ, !storeGS Σ}.

Implicit Types skI skR : sign_key.

Lemma db_main_alloc skI skR :
  term_token skI (↑dbN.@"client".@(skR : term).@"replica") ==∗
  db_main skI skR ∅ ∗ db_sync skI skR ∅.
Proof.
iIntros "token".
iMod (rep_main_alloc with "token") as "(? & ? & _)"; eauto.
by iFrame.
Qed.

Lemma db_copy_alloc skI skR :
  term_token skR (↑dbN.@"server".@(skI : term)) ==∗ db_copy skI skR ∅.
Proof.
iIntros "token".
iMod (rep_copy_alloc with "token") as "[? _]"; eauto.
Qed.

Lemma db_main_update db' skI skR db :
  db_main skI skR db -∗
  db_sync skI skR db ==∗
  db_main skI skR db' ∗
  db_update skI skR db db'.
Proof. exact: rep_main_update. Qed.

Lemma db_copy_update skI skR db1 db2 db' :
  db_copy skI skR db1 -∗
  db_update skI skR db2 db' ==∗
  ⌜db1 = db2⌝ ∗
  db_copy skI skR db' ∗
  db_sync skI skR db'.
Proof. exact: rep_copy_update. Qed.

Lemma db_main_sync skI skR db db' :
  db_main skI skR db -∗
  db_sync skI skR db' -∗
  ⌜db = db'⌝.
Proof. exact: rep_main_sync. Qed.

End DbMainResources.

End Section_8_KeyValueStore.

Section Section_9_Implementation.

Context `{!heapGS Σ, !cryptisGS Σ}.

(**

The [init_network] function is responsible for allocating the network channel
and launching the attacker threads.  It is called by the [run_network] function,
which appears in the security proofs for all the games above.

*)

Lemma wp_init_network :
  cryptis_ctx -∗
  WP init_network #() {{ c, channel c }}.
Proof.
iIntros "#ctx". wp_apply wp_init_network; eauto.
Qed.

End Section_9_Implementation.

Print Assumptions nsl_secure.
Print Assumptions iso_secure.
Print Assumptions store_secure.
