From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap list excl.
From iris.algebra Require Import functions.
From iris.base_logic.lib Require Import invariants.
From iris.bi Require Import fixpoint_mono.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib.
From cryptis.lib Require Import gmeta nown saved_prop.
From cryptis.core Require Import term minted.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* MOVE *)
Variant functionality := AENC | SIGN | SENC.

Definition func_of_key_type kt :=
  match kt with
  | AEnc | ADec => AENC
  | Sign | Verify => SIGN
  | SEnc => SENC
  end.

Definition func_of_term t :=
  match t with
  | TKey kt _ => Some (func_of_key_type kt)
  | _ => None
  end.
(* /MOVE *)

Class publicGpreS Σ := PublicGPreS {
  publicGpreS_nonce : savedPredG Σ term;
  publicGpreS_seal  : savedPredG Σ (term * term);
  publicGpreS_meta  : metaGS Σ;
}.

Local Existing Instance publicGpreS_nonce.
Local Existing Instance publicGpreS_seal.
Local Existing Instance publicGpreS_meta.

Class publicGS Σ := PublicGS {
  public_inG : publicGpreS Σ;
  public_hash_name  : gname;
  public_aenc_name  : gname;
  public_sign_name  : gname;
  public_senc_name  : gname;
}.

Global Existing Instance public_inG.

Definition publicΣ : gFunctors :=
  #[savedPredΣ term;
    savedPredΣ (key_type * term);
    savedPredΣ (term * term);
    metaΣ].

Global Instance subG_publicGpreS Σ : subG publicΣ Σ → publicGpreS Σ.
Proof. solve_inG. Qed.

Section Public.

Context `{!heapGS Σ, !publicGS Σ}.
Notation iProp := (iProp Σ).
Notation iPropO := (iPropO Σ).
Notation iPropI := (iPropI Σ).

Definition pnonce a : iProp :=
  ∃ γ P, meta a (nroot.@"nonce") γ ∧
         own γ (saved_pred DfracDiscarded P) ∧
         ▷ □ P (TNonce a).

Global Instance Persistent_pnonce a : Persistent (pnonce a).
Proof. apply _. Qed.

Definition dh_pred_base (t t' : term) : iProp :=
  match t with
  | TNonce a =>
    ∃ γ φ, meta a (nroot.@"dh") γ ∧
           own γ (saved_pred DfracDiscarded φ) ∧
           ▷ □ φ t'
  | _ => ▷ False
  end.

Lemma dh_pred_base_TInv t t' :
  ¬ is_inv t →
  dh_pred_base (TInv t) t' ⊣⊢ ▷ False.
Proof.
rewrite -{1}[t]TInvK is_inv_TInv is_inv_unfold.
case: (TInv t) => //=; eauto.
Qed.

Global Instance dh_pred_base_persistent t t' :
  Persistent (dh_pred_base t t').
Proof. by case: t; apply _. Qed.

Definition dh_pred0_pre P DH ts : iProp :=
  dh_pred_base ts.1 ts.2 ∨
  P ts.1 ∨
  ∃ t2' t, ⌜ts.2 = TExp t2' t⌝ ∗ ⌜TInv t ∉ exps t2'⌝ ∗
  DH (ts.1, t2') ∗ DH (t, ts.2).

Local Instance dh_pred0_pre_mono P : BiMonoPred (dh_pred0_pre P).
Proof.
constructor; last by move=> ??; solve_proper.
iIntros (DH1 DH2 _ _) "#H %ts dh"; rewrite /dh_pred0_pre.
iDestruct "dh" as "[? | [? | dh]]"; eauto.
iDestruct "dh" as (t2 t') "(#p & #? & dh1 & dh2)".
iRight; iRight; iExists t2, t'; iFrame "#".
by iSplitL "dh1"; iApply "H".
Qed.

Local Definition dh_pred0_def : (term → iProp) → term * term → iProp :=
  λ P, bi_least_fixpoint (dh_pred0_pre P).
Local Definition dh_pred0_aux : seal dh_pred0_def. Proof. by eexists. Qed.
Definition dh_pred0 := dh_pred0_aux.(unseal).
Local Lemma dh_pred0_unseal : dh_pred0 = dh_pred0_def.
Proof. by rewrite -dh_pred0_aux.(seal_eq). Qed.

Lemma dh_pred0_unfold P ts :
  dh_pred0 P ts ⊣⊢
  dh_pred_base ts.1 ts.2 ∨
  P ts.1 ∨
  ∃ t2' t, ⌜ts.2 = TExp t2' t⌝ ∗ ⌜TInv t ∉ exps t2'⌝ ∗
  dh_pred0 P (ts.1, t2') ∗ dh_pred0 P (t, ts.2).
Proof. by rewrite dh_pred0_unseal /dh_pred0_def least_fixpoint_unfold. Qed.

Lemma dh_pred0_ind P φ :
  □ (∀ ts, dh_pred0_pre P (λ ts, φ ts ∧ dh_pred0 P ts) ts -∗ φ ts) -∗
  ∀ ts, dh_pred0 P ts -∗ φ ts.
Proof.
rewrite dh_pred0_unseal; iApply least_fixpoint_ind; solve_proper.
Qed.

Global Instance dh_pred0_ne n :
  Proper (pointwise_relation _ (dist n) ==> dist n ==> dist n) dh_pred0.
Proof.
move=> P1 P2 HP ts1 ts2 e.
have -> : ts1 = ts2 by apply leibniz_equiv_iff.
rewrite dh_pred0_unseal; apply least_fixpoint_ne; solve_proper.
Qed.

Global Instance dh_pred0_proper :
  Proper (pointwise_relation _ (≡) ==> (≡) ==> (≡)) dh_pred0.
Proof.
move=> P1 P2 HP ts1 ts2 e.
have -> : ts1 = ts2 by apply leibniz_equiv_iff.
apply equiv_dist => n.
apply dh_pred0_ne => // ts'.
apply equiv_dist; apply: HP.
Qed.

Global Instance dh_pred0_persistent P :
  (∀ ts, Persistent (P ts)) →
  ∀ ts, Persistent (dh_pred0 P ts).
Proof.
rewrite {2}/Persistent => HP ts; iIntros "H".
iRevert (ts) "H".
iApply dh_pred0_ind; iIntros "!> %ts [#? | [#? | H]]"; eauto.
- rewrite dh_pred0_unfold; eauto.
- rewrite dh_pred0_unfold; eauto.
- iDestruct "H" as (t2' t) "(% & % & [#? _] & [#? _])".
  iModIntro; rewrite [dh_pred0 P ts]dh_pred0_unfold.
  by iRight; iRight; iExists t2', t; iFrame "#".
Qed.

Lemma dh_pred0_wand P1 P2 :
  □ (∀ t, P1 t -∗ P2 t) -∗
  ∀ ts, dh_pred0 P1 ts -∗ dh_pred0 P2 ts.
Proof.
iIntros "#mono".
iApply dh_pred0_ind; iIntros "!> %ts [? | [? | H]]"; eauto.
- by rewrite dh_pred0_unfold; iLeft.
- by rewrite dh_pred0_unfold; iRight; iLeft; iApply "mono".
- iDestruct "H" as (t2' t) "(% & % & [? _] & [? _])".
  rewrite [dh_pred0 P2 ts]dh_pred0_unfold.
  by iRight; iRight; iExists t2', t; iFrame.
Qed.

Definition name_of_functionality F :=
  match F with
  | AENC => public_aenc_name
  | SIGN => public_sign_name
  | SENC => public_senc_name
  end.

Definition seal_pred F N Φ : iProp :=
  nown (name_of_functionality F) N
    (saved_pred DfracDiscarded (fun '(k, t) => Φ k t)).

Definition aenc_pred N (Φ : aenc_key → term → iProp) :=
  seal_pred AENC N (λ k t, ∃ k' : aenc_key, ⌜k = k'⌝ ∗ Φ k' t)%I.

Definition sign_pred N (Φ : sign_key → term → iProp) :=
  seal_pred SIGN N (λ k t, ∃ k' : sign_key, ⌜k = k'⌝ ∗ Φ k' t)%I.

Definition senc_pred N (Φ : senc_key → term → iProp) :=
  seal_pred SENC N (λ k t, ∃ k' : senc_key, ⌜k = k'⌝ ∗ Φ k' t)%I.

Definition seal_pred_token F E :=
  gmeta_token (name_of_functionality F) E.

Lemma seal_pred_token_difference F E1 E2 :
  E1 ⊆ E2 →
  seal_pred_token F E2 ⊣⊢ seal_pred_token F E1 ∗ seal_pred_token F (E2 ∖ E1).
Proof.
move=> sub; rewrite /seal_pred_token; exact: gmeta_token_difference.
Qed.

Lemma seal_pred_token_drop E1 E2 F :
  E1 ⊆ E2 →
  seal_pred_token F E2 -∗
  seal_pred_token F E1.
Proof.
iIntros (sub) "t".
rewrite seal_pred_token_difference //.
by iDestruct "t" as "[t _]".
Qed.

Global Instance seal_pred_persistent F N Φ : Persistent (seal_pred F N Φ).
Proof. apply _. Qed.

Lemma seal_pred_agree k t F N Φ1 Φ2 :
  seal_pred F N Φ1 -∗
  seal_pred F N Φ2 -∗
  ▷ (Φ1 k t ≡ Φ2 k t).
Proof.
rewrite /seal_pred. iIntros "#own1 #own2".
iPoseProof (nown_valid_2 with "own1 own2") as "#valid".
iPoseProof (saved_pred_op_validI with "valid") as "[_ #agree]".
by iApply ("agree" $! (k, t)).
Qed.

Lemma seal_pred_set F E (N : namespace) Φ :
  ↑N ⊆ E →
  seal_pred_token F E ==∗
  seal_pred F N Φ ∗
  seal_pred_token F (E ∖ ↑N).
Proof. iIntros (?) "token". by iApply nown_alloc. Qed.

Lemma aenc_pred_set E N Φ :
  ↑N ⊆ E →
  seal_pred_token AENC E ==∗
  aenc_pred N Φ ∗
  seal_pred_token AENC (E ∖ ↑N).
Proof. move=> ?. by iApply seal_pred_set. Qed.

Lemma sign_pred_set E N Φ :
  ↑N ⊆ E →
  seal_pred_token SIGN E ==∗
  sign_pred N Φ ∗
  seal_pred_token SIGN (E ∖ ↑N).
Proof. move=> ?. by iApply seal_pred_set. Qed.

Lemma senc_pred_set E N Φ :
  ↑N ⊆ E →
  seal_pred_token SENC E ==∗
  senc_pred N Φ ∗
  seal_pred_token SENC (E ∖ ↑N).
Proof. move=> ?. by iApply seal_pred_set. Qed.

Definition wf_seal F k t : iProp :=
  ∃ N t' Φ, ⌜t = Spec.tag (Tag N) t'⌝ ∧ seal_pred F N Φ ∧ □ ▷ Φ k t'.

Global Instance wf_seal_persistent F k t : Persistent (wf_seal F k t).
Proof. by apply _. Qed.

Lemma wf_seal_elim F k N t Φ :
  wf_seal F k (Spec.tag (Tag N) t) -∗
  seal_pred F N Φ -∗
  □ ▷ Φ k t.
Proof.
iDestruct 1 as (N' t' Φ') "(%t_t' & #HΦ' & #inv)"; iIntros "#HΦ".
case/Spec.tag_inj: t_t' => /Tag_inj <- <-.
iPoseProof (seal_pred_agree k t with "HΦ HΦ'") as "e".
by iIntros "!> !>"; iRewrite "e".
Qed.

Definition hash_pred N (P : term → iProp) : iProp :=
  nown public_hash_name N (saved_pred DfracDiscarded P).

Definition hash_pred_token E :=
  gmeta_token public_hash_name E.

Lemma hash_pred_token_difference E1 E2 :
  E1 ⊆ E2 →
  hash_pred_token E2 ⊣⊢ hash_pred_token E1 ∗ hash_pred_token (E2 ∖ E1).
Proof.
move=> sub; rewrite /hash_pred_token; exact: gmeta_token_difference.
Qed.

Lemma hash_pred_token_drop E1 E2 :
  E1 ⊆ E2 →
  hash_pred_token E2 -∗
  hash_pred_token E1.
Proof.
iIntros (sub) "t".
rewrite hash_pred_token_difference //.
by iDestruct "t" as "[t _]".
Qed.

Global Instance hash_pred_persistent N P : Persistent (hash_pred N P).
Proof. apply _. Qed.

Lemma hash_pred_agree t N P₁ P₂ :
  hash_pred N P₁ -∗
  hash_pred N P₂ -∗
  ▷ (P₁ t ≡ P₂ t).
Proof.
rewrite /hash_pred. iIntros "#own1 #own2".
iPoseProof (nown_valid_2 with "own1 own2") as "#valid".
iPoseProof (saved_pred_op_validI with "valid") as "[_ #agree]".
by iApply ("agree" $! t).
Qed.

Lemma hash_pred_set E N P :
  ↑N ⊆ E →
  hash_pred_token E ==∗
  hash_pred N P ∗
  hash_pred_token (E ∖ ↑N).
Proof. iIntros (?) "token". by iApply nown_alloc. Qed.

Definition wf_hash t : iProp :=
  ∃ N t' P, ⌜t = Spec.tag (Tag N) t'⌝ ∧ hash_pred N P ∧ □ ▷ P t'.

Global Instance wf_hash_persistent t : Persistent (wf_hash t).
Proof. by apply _. Qed.

Lemma wf_hash_elim N t P :
  wf_hash (Spec.tag (Tag N) t) -∗
  hash_pred N P -∗
  □ ▷ P t.
Proof.
iDestruct 1 as (N' t' P') "(%t_t' & #HP' & #inv)"; iIntros "#HP".
case/Spec.tag_inj: t_t' => /Tag_inj <- <-.
iPoseProof (hash_pred_agree t with "HP HP'") as "e".
by iIntros "!> !>"; iRewrite "e".
Qed.

Inductive decompose (T : gset term) (t : term) : Prop :=
| DInt n of T = ∅ & t = TInt n

| DPair t1 t2 of T = {[t1; t2]} & t = TPair t1 t2

| DKey kt t' of T = {[t']} & t = TKey kt t'

| DSeal k t' of T = {[k; t']} & t = TSeal k t'

| DHash t' of T = {[t']} & t = THash t'

| DInv t' of T = {[t']} & ¬ is_inv t' & is_inv t & t = TInv t'

| DExp t1 t2 of T = {[t1; t2]} & TInv t2 ∉ exps t1 & is_exp t & t = TExp t1 t2.

Lemma decompose_tsize T t t' : decompose T t → t' ∈ T → tsize t' < tsize t.
Proof.
case; try by move =>> -> -> //;
          try move => /elem_of_union [];
          move => /elem_of_singleton ->;
          rewrite [tsize (_ _)]tsizeE -?ssrnat.plusE;
          lia.
- move => ? -> /negb_True /is_trueP ? _ -> /elem_of_singleton ->;
  rewrite [tsize (_ _)]tsizeE //; lia.
- by move => ?? -> /tsize_lt_TExp [??] _ -> /elem_of_union [] /elem_of_singleton ->.
Qed.

Fixpoint public_pre_aux P n t : iProp :=
  if n is S n then
    minted t ∧ (
     (∃ T, ⌜decompose T t⌝ ∧ [∗ set] t' ∈ T, public_pre_aux P n t')
     ∨ (⌜is_exp t⌝ ∧
        [∗ list] t' ∈ exps t,
          dh_pred0 P (t', t) ∧ □ (public_pre_aux P n t' → public_pre_aux P n (TExp t (TInv t'))))
     ∨ match t with
       | TNonce a => ◇ pnonce a
       | TKey kt t => ⌜Spec.public_key_type kt⌝
       | THash t => wf_hash t
       | TSeal k t =>
           match func_of_term k with
           | Some F =>
               ⌜Spec.is_seal_key k⌝ ∧
               wf_seal F (Spec.skey k) t ∧
               match Spec.open_key k with
               | Some k' => □ (public_pre_aux P n k' → public_pre_aux P n t)
               | None => True
               end
           | None => True
           end
       | _ => False
       end%I
    )
  else False.

Lemma Persistent_public_pre_aux P n t :
  □ (∀ t, P t -∗ <pers> P t) -∗
  public_pre_aux P n t -∗ <pers> public_pre_aux P n t.
Proof.
elim: n => [|n IH] //= in t *; eauto.
iIntros "#wand [#m H]"; iSplit => //.
iDestruct "H" as "[H | [H | H]]".
- iDestruct "H" as (T ?) "H"; iLeft; iExists T; iSplit; eauto.
  iAssert ([∗ set] t' ∈ T, <pers> public_pre_aux P n t')%I as "{H} #H".
  { iApply (big_sepS_impl with "H"). iIntros "!> %t' _".
    by iApply IH. }
  by iModIntro; iApply (big_sepS_impl with "H"); eauto.
- iDestruct "H" as "(% & H)"; iRight; iLeft.
  set (P' := public_pre_aux P n).
  iAssert ([∗ list] t' ∈ exps t, <pers> dh_pred0 P (t', t) ∧
    □ (P' t' → P' (TExp t (TInv t'))))%I as "{H} #H".
  { iApply (big_sepL_impl with "H").
    iIntros "!> %k %t' _ [dh #?]"; iSplit => //.
    iAssert (dh_pred0 (λ t'', <pers> P t'')%I (t', t)) as "{dh} #dh".
    { iApply (dh_pred0_wand with "[] dh"); eauto. }
    by iModIntro; iApply (dh_pred0_wand with "[] dh"); iIntros "!> % #?". }
  iModIntro; iSplit => //.
  by iApply (big_sepL_impl with "H"); iIntros "!> % % _ [#? #?]"; eauto.
- iRight; iRight; case: t; by move=> *; iPoseProof "H" as "#H".
Qed.

Global Instance public_pre_aux_ne n :
  Proper (pointwise_relation _ (dist n) ==> dist n ==> dist n ==> dist n) public_pre_aux.
Proof.
move=> P1 P2 HP m _ <- t _ <-; elim: m => //= m IH in t *.
f_equiv; f_equiv; last f_equiv.
- f_equiv => T.
  by f_equiv; f_equiv => t'.
- f_equiv.
  f_equiv=> ? ?; f_equiv; first by f_equiv.
  by f_equiv; f_equiv.
- case: t => //= k t.
  case: func_of_term => // F.
  f_equiv; f_equiv.
  case e_k: Spec.open_key => [k'|] //.
  by rewrite !IH.
Qed.

Definition public_pre P t := public_pre_aux P (tsize t) t.

Global Instance public_pre_ne n :
  Proper (pointwise_relation _ (dist n) ==> dist n ==> dist n) public_pre.
Proof.
rewrite /public_pre => P1 P2 HP t _ <-; by f_equiv.
Qed.

Lemma Persistent_public_pre P t :
  □ (∀ t, P t -∗ <pers> P t) -∗
  public_pre P t -∗ <pers> public_pre P t.
Proof. exact: Persistent_public_pre_aux. Qed.

Lemma open_key_tsize t1 t2 : Spec.open_key t1 = Some t2 → tsize t2 = tsize t1.
Proof.
by case: t1 => // - [] //= t [<-]; rewrite tsizeE.
Qed.

Lemma public_pre_aux_eq P n t : tsize t ≤ n → public_pre_aux P n t ⊣⊢ public_pre P t.
Proof.
rewrite /public_pre.
elim: n / (lt_wf n) t => - [|n] _ IH t t_n /=;
move: (ssrbool.elimT ssrnat.ltP (tsize_gt0 t)) => H;
first lia.
case e_st: (tsize t) => [|m] /=; first lia.
apply: bi.and_proper => // {H}.
do !apply bi.or_proper.
- apply: bi.exist_proper => T.
  apply: and_proper_L => T_t.
  apply: big_sepS_proper => t' T_t'.
  move: (decompose_tsize T_t T_t') => ?.
  rewrite (IH n) ?(IH m) //; lia.
- apply bi.and_proper => //.
  apply big_sepL_proper => _ t' /(elem_of_list_lookup_2 _ _ _) /tsize_TExp_TInv ?.
  by rewrite !IH; try lia.
- case: t t_n e_st => //= k t t_n e_st.
  case: func_of_term => // F.
  apply: bi.and_proper => //.
  apply: bi.and_proper => //.
  case e_k: Spec.open_key => [k'|] //.
  have ? := open_key_tsize e_k.
  have ?: tsize (TSeal k t) = S (tsize k + tsize t).
    by rewrite tsizeE -ssrnat.plusE.
  rewrite !(IH n) ?(IH m) //; lia.
Qed.

(* TODO: Merge with public_pre_aux_eq *)
Lemma public_pre_eq P t :
  public_pre P t ⊣⊢
  minted t ∧ (
      (∃ T, ⌜decompose T t⌝ ∧ [∗ set] t' ∈ T, public_pre P t')
     ∨ (⌜is_exp t⌝ ∧
        [∗ list] t' ∈ exps t,
          dh_pred0 P (t', t) ∧ □ (public_pre P t' → public_pre P (TExp t (TInv t'))))
     ∨ match t with
       | TNonce a => ◇ pnonce a
       | TKey kt t => ⌜Spec.public_key_type kt⌝
       | THash t => wf_hash t
       | TSeal k t =>
           match func_of_term k with
           | Some F =>
               ⌜Spec.is_seal_key k⌝ ∧
               wf_seal F (Spec.skey k) t ∧
               match Spec.open_key k with
               | Some k' => □ (public_pre P k' → public_pre P t)
               | None => True
               end
           | None => True
           end
       | _ => False
       end%I
  ).
Proof.
rewrite {1}/public_pre.
case e_st: (tsize t) => [|m] /=.
  move: (ssrbool.elimT ssrnat.ltP (tsize_gt0 t)) => H; lia.
apply: bi.and_proper => //.
do !apply bi.or_proper.
- apply: bi.exist_proper => T.
  apply: and_proper_L => T_t.
  apply: big_sepS_proper => t' T_t'.
  move: (decompose_tsize T_t T_t') => ?.
  rewrite public_pre_aux_eq //; lia.
- apply bi.and_proper => //.
  apply big_sepL_proper => k t' /(elem_of_list_lookup_2 _ _ _) /tsize_TExp_TInv ?.
  by rewrite !public_pre_aux_eq; try lia.
- case: t e_st => //= k t e_st.
  rewrite tsizeE -ssrnat.plusE in e_st.
  case: func_of_term => // F.
  apply: bi.and_proper => //.
  apply: bi.and_proper => //.
  case e_k: Spec.open_key => [k'|] //=.
  have ? := open_key_tsize e_k.
  rewrite !public_pre_aux_eq //; lia.
Qed.

Definition public_pre' (P : term -d> iProp) : term -d> iProp :=
  public_pre (λ t, ▷ P t)%I.

Local Instance public_pre'_contractive : Contractive public_pre'.
Proof. rewrite /public_pre'; solve_contractive. Qed.

Definition public_def := fixpoint public_pre'.
Local Definition public_aux : seal (@public_def). Proof. by eexists. Qed.
Definition public := public_aux.(unseal).
Local Lemma public_unseal : public = public_def.
Proof. rewrite -public_aux.(seal_eq) //. Qed.

Definition dh_pred_def := λ t1 t2, dh_pred0 (λ t, ▷ public t)%I (t1, t2).
Local Definition dh_pred_aux : seal (@dh_pred_def). Proof. by eexists. Qed.
Definition dh_pred := dh_pred_aux.(unseal).
Local Lemma dh_pred_unseal : dh_pred = dh_pred_def.
Proof. rewrite -dh_pred_aux.(seal_eq) //. Qed.

Lemma public_eq t :
  public t ⊣⊢
  minted t ∧ (
      (∃ T, ⌜decompose T t⌝ ∧ [∗ set] t' ∈ T, public t')
     ∨ (⌜is_exp t⌝ ∧
        [∗ list] t' ∈ exps t,
          dh_pred t' t ∧ □ (public t' → public (TExp t (TInv t'))))
     ∨ match t with
       | TNonce a => ◇ pnonce a
       | TKey kt t => ⌜Spec.public_key_type kt⌝
       | THash t => wf_hash t
       | TSeal k t =>
           match func_of_term k with
           | Some F =>
               ⌜Spec.is_seal_key k⌝ ∧
               wf_seal F (Spec.skey k) t ∧
               match Spec.open_key k with
               | Some k' => □ (public k' → public t)
               | None => True
               end
           | None => True
           end
       | _ => False
       end%I
  ).
Proof.
rewrite public_unseal dh_pred_unseal /public_def.
rewrite (fixpoint_unfold public_pre' t) {1}/public_pre' public_pre_eq.
f_equiv; f_equiv; last f_equiv.
- f_equiv => ?.
  f_equiv; f_equiv=> ?; by rewrite (fixpoint_unfold public_pre' _).
- f_equiv; f_equiv => ? ?; f_equiv.
  + by rewrite /dh_pred_def public_unseal.
  + by rewrite !(fixpoint_unfold public_pre' _).
- case: t => // k t.
  case: func_of_term => // ?.
  f_equiv; f_equiv; case: Spec.open_key => // ?.
  by rewrite !(fixpoint_unfold public_pre' _).
Qed.

Global Instance Persistent_public t : Persistent (public t).
Proof.
rewrite /Persistent; rewrite public_unseal /public_def.
iIntros "H"; iLöb as "IH" forall (t).
rewrite (fixpoint_unfold public_pre' t) {3 4}/public_pre'.
iApply (Persistent_public_pre with "[] H").
iIntros "!> % H"; rewrite -bi.later_persistently; iModIntro.
by iApply "IH".
Qed.

Global Instance Persistent_dh_pred t1 t2 : Persistent (dh_pred t1 t2).
Proof. rewrite dh_pred_unseal /dh_pred_def. by apply _. Qed.

Lemma dh_pred_intro1 t1 t2 : dh_pred_base t1 t2 -∗ dh_pred t1 t2.
Proof.
rewrite dh_pred_unseal /dh_pred_def dh_pred0_unfold /=.
by eauto.
Qed.

Lemma dh_pred_intro2 t t1 t2 :
  TInv t ∉ exps t2 →
  dh_pred t1 t2 -∗ dh_pred t (TExp t2 t) -∗ dh_pred t1 (TExp t2 t).
Proof.
rewrite dh_pred_unseal /dh_pred_def (dh_pred0_unfold _ (t1, TExp t2 t)) /=.
by iIntros "% #H1 #H2"; iRight; iRight; iExists _, _; iFrame "#"; eauto.
Qed.

Lemma dh_pred_intro3 t1 t2 : ▷ public t1 -∗ dh_pred t1 t2.
Proof.
rewrite dh_pred_unseal /dh_pred_def dh_pred0_unfold /=.
by eauto.
Qed.

Lemma dh_pred_ind (φ : term → term → iProp) :
  (□ ∀ t1 t2, dh_pred_base t1 t2 -∗ φ t1 t2) -∗
  (□ ∀ t t1 t2, ⌜TInv t ∉ exps t2⌝ -∗
                dh_pred t1 t2 -∗ φ t1 t2 -∗
                dh_pred t (TExp t2 t) -∗ φ t (TExp t2 t) -∗
                φ t1 (TExp t2 t)) -∗
  (□ ∀ t1 t2, ▷ public t1 -∗ φ t1 t2) -∗
  ∀ t1 t2, dh_pred t1 t2 -∗ φ t1 t2.
Proof.
iIntros "#H1 #H2 #H3 %t1 %t2".
rewrite dh_pred_unseal /dh_pred_def; set ts := (t1, t2).
rewrite -[t1]/ts.1 -[t2]/ts.2; move: ts => ts.
iRevert (ts); iApply dh_pred0_ind.
iIntros "!> %ts [? | [? | H]]".
- by iApply "H1".
- by iApply "H3".
- iDestruct "H" as (t2' t) "/= (-> & % & [H11 #H12] & [H21 #H22])".
  by iApply ("H2" with "[//] H12 H11 [$]").
Qed.

Lemma dh_pred_inv_gen ts t1 t2 :
  t1 ∈ ts →
  ts ⊆ exps t2 →
  dh_pred t1 t2 -∗
  ∃ t, ⌜t ∈ ts⌝ ∧ (
    ▷ public t ∨
    ∃ t3, ⌜base t3 = base t2⌝ ∧ ⌜ts ⊆ exps t3⌝ ∧ dh_pred_base t t3).
Proof.
iIntros "%t1_ts %ts_t2 dh"; iRevert (ts t1_ts ts_t2); iRevert (t1 t2) "dh".
iApply dh_pred_ind; eauto 10.
iIntros "!> %t %t1 %t2 %t_t2 #dh_t1 IH_t1 #dh_t IH_t %ts %t1_ts %ts_t2'".
rewrite base_TExpN; case: (decide (t ∈ ts)) => t_ts; first by iApply "IH_t".
iApply "IH_t1"; iPureIntro => // t3 t3_ts.
have := ts_t2' _ t3_ts.
rewrite -!count_exp_gt0 count_exp_TExp decide_False; last by congruence.
case: decide => ?; lia.
Qed.

Lemma dh_pred_inv t1 t2 :
  t1 ∈ exps t2 →
  dh_pred t1 t2 -∗
  ∃ t, ⌜t ∈ exps t2⌝ ∧ (
    ▷ public t ∨
    ∃ t3, ⌜base t3 = base t2⌝ ∧ ⌜exps t2 ⊆ exps t3⌝ ∧ dh_pred_base t t3).
Proof. by move=> t1_t2; iApply dh_pred_inv_gen. Qed.

Lemma dh_pred_inv_same' t1 t2 :
  dh_pred t1 t2 -∗
  ▷ public t1 ∨ ∃ t2', ⌜base t2' = base t2⌝ ∗ dh_pred_base t1 t2'.
Proof.
iRevert (t1 t2); iApply dh_pred_ind; eauto.
- by iIntros "!> %t1 %t2 #base"; eauto.
- by iIntros "!> %t %t1 %t2 _ _ #IH _ _"; rewrite base_TExpN.
Qed.

Lemma dh_pred_inv_same t1 t2 :
  t1 ∈ exps t2 →
  dh_pred t1 t2 -∗
  ▷ public t1 ∨
  ∃ t2', ⌜base t2' = base t2⌝ ∗ ⌜t1 ∈ exps t2'⌝ ∗ dh_pred_base t1 t2'.
Proof.
iIntros "%t1_t2 dh"; iRevert (t1_t2); iRevert (t1 t2) "dh".
iApply dh_pred_ind; last by eauto.
- iIntros "!> %t1 %t2 #dh %t1_t2"; eauto.
- iIntros "!> %t %t1 %t2 _ _ IH1 _ IH2 %t1_t2"; rewrite base_TExpN.
  case: (decide (t = t1)) => [e|ne].
    by move: e => -> {t} in t1_t2 *; iApply "IH2".
  iApply "IH1"; iPureIntro.
  move: t1_t2; rewrite -!count_exp_gt0 count_exp_TExp decide_False //.
  by case: decide; lia.
Qed.

Lemma public_minted t : public t ⊢ minted t.
Proof. rewrite public_eq; by iIntros "[??]". Qed.

Lemma public_TInt n : public (TInt n) ⊣⊢ True.
Proof.
apply: (anti_symm _); iIntros "_" => //.
rewrite public_eq minted_TInt; iSplit => //.
iLeft; iExists ∅; rewrite big_sepS_empty; iSplit => //.
by iPureIntro; econstructor.
Qed.

Lemma public_TPair t1 t2 : public (TPair t1 t2) ⊣⊢ public t1 ∧ public t2.
Proof.
apply: (anti_symm _); iIntros "#Ht" => //.
- rewrite public_eq minted_TPair.
  iDestruct "Ht" as "([Ht1 Ht2] & publ)".
  iDestruct "publ" as "[publ | [(? & _) | publ]]" => //=.
  iDestruct "publ" as (T) "[%dec publ]".
  case: dec => //= {}t1 {}t2 -> [-> ->].
  by rewrite big_sepS_union_pers !big_sepS_singleton.
- iDestruct "Ht" as "[Ht1 Ht2]".
  rewrite [public (TPair t1 t2)]public_eq minted_TPair -!public_minted.
  iSplit; eauto.
  iLeft; iExists _; iSplit.
    iPureIntro; by econstructor.
  by rewrite big_sepS_union_pers !big_sepS_singleton; eauto.
Qed.

Lemma public_TNonce a :
  public (TNonce a) ⊣⊢ ◇ pnonce a ∗ meta a (nroot.@"minted") ().
Proof.
apply: (anti_symm _); iIntros "Ht".
- rewrite public_eq; iDestruct "Ht" as "[? Ht]".
  rewrite minted_TNonce. iFrame.
  iDestruct "Ht" as "[publ | [ (? & _) | ? ]]" => //.
  iDestruct "publ" as (T) "[%dec _]".
  by case: dec.
- rewrite public_eq minted_TNonce /pnonce.
  iDestruct "Ht" as "[Ht ?]". iFrame.
Qed.

Lemma public_TKey kt t :
  public (TKey kt t) ⊣⊢ public t ∨ minted t ∧ ⌜Spec.public_key_type kt⌝.
Proof.
apply: (anti_symm _).
- rewrite public_eq minted_TKey; iDestruct 1 as "[Ht publ]".
  iDestruct "publ" as "[publ | [(? & _) | publ]]" => //.
  + iDestruct "publ" as (T) "[%dec publ]".
    case: dec => //= {}kt {}t -> [-> ->].
    by rewrite big_sepS_singleton; eauto.
  + by eauto.
- iDestruct 1 as "# [publ | [s_t publ]]".
    rewrite [public (TKey _ _)]public_eq minted_TKey -public_minted.
    iSplit => //; iLeft.
    iExists {[t]}; iSplit; first by iPureIntro; econstructor.
    by rewrite big_sepS_singleton.
  rewrite public_eq; iSplit; eauto.
  by rewrite minted_TKey.
Qed.

Lemma public_TSeal k t :
  public (TSeal k t) ⊣⊢
  public k ∧ public t ∨
  minted (TSeal k t) ∧
  match func_of_term k with
  | Some F =>
      ⌜Spec.is_seal_key k⌝ ∧
      wf_seal F (Spec.skey k) t ∧
      match Spec.open_key k with
      | Some k' => □ (public k' → public t)
      | None => True
      end
  | None => True
  end.
Proof.
apply: (anti_symm _).
- rewrite public_eq minted_TSeal.
  iDestruct 1 as "[[Hk Ht] publ]".
  iDestruct "publ" as "[publ | [(? & _) | publ]]" => //.
  + iDestruct "publ" as (T) "[%dec ?]".
    case: dec => // {}k {}t -> [-> ->].
    by rewrite big_sepS_union_pers !big_sepS_singleton; iLeft.
  + iRight. iSplit; first by eauto.
    by case: k => // kt k.
- iDestruct 1 as "[#[Hk Ht] | (#Ht & inv)]".
  { rewrite [public (TSeal _ _)]public_eq minted_TSeal.
    rewrite -!public_minted.
    iSplit; eauto; iLeft.
    iExists {[k; t]}; rewrite big_sepS_union_pers !big_sepS_singleton.
    iSplit; eauto; iPureIntro; by econstructor. }
  rewrite [public (TSeal _ _)]public_eq; iSplit => //. by eauto.
Qed.

Lemma public_open k t t' :
  Spec.open k t = Some t' →
  public k -∗
  public t -∗
  public t'.
Proof.
rewrite /Spec.open.
case: t => // k_t t.
rewrite public_TSeal.
case: decide => // k_t_k [<-]. rewrite k_t_k.
iIntros "p_k [[??]|(? & p_t)] //".
case e: func_of_term => [F|].
- iDestruct "p_t" as "(_ & _ & p_t)". by iApply "p_t".
- by case: k_t => // ?? in k_t_k e *.
Qed.

Lemma public_THash t :
  public (THash t) ⊣⊢ public t ∨ minted t ∧ wf_hash t.
Proof.
apply: (anti_symm _).
- rewrite public_eq minted_THash.
  iDestruct 1 as "[Ht [publ | [(? & _) | publ]]]" => //; eauto.
  iDestruct "publ" as (T) "[%dec ?]".
  case: dec => //= {}t -> [->].
  by rewrite big_sepS_singleton; eauto.
- iDestruct 1 as "[Ht | [? publ]]".
    rewrite [public (THash _)]public_eq minted_THash -public_minted.
    iSplit => //=; iLeft.
    iExists {[t]}; rewrite big_sepS_singleton; iSplit => //.
    iPureIntro; by econstructor.
  rewrite public_eq; iSplit.
    by rewrite minted_THash.
  by eauto.
Qed.

Lemma public_THashIS N φ t :
  hash_pred N φ -∗
  minted t -∗
  ▷ □ φ t -∗
  public (THash (Spec.tag (Tag N) t)).
Proof.
  iIntros "#Hpred #Hminted #Hφ".
  rewrite public_THash.
  iRight.
  rewrite minted_tag. iSplit => //.
  iExists _, _, _.
  eauto.
Qed.

Lemma public_TInv t : public (TInv t) ⊣⊢ public t.
Proof.
wlog: t/ ¬ is_inv t.
{ move => H. case inv_t: (is_inv t).
  + rewrite -{2}[t]TInvK (H (TInv t)) // is_inv_TInv inv_t. exact /neg_false.
  + apply H. rewrite inv_t. exact /neg_false. }
move => /[dup] ? /negb_True; rewrite -is_inv_TInv => invt.
apply: anti_symm; rewrite [public (TInv t)]public_eq minted_TInv.
- have ?: ¬ is_exp (TInv t) by move => /is_trueP /(ssrbool.contraLR (is_exp_TInv t)) /is_trueP.
  iIntros "(_ & [dec | [(% & _) | ?]])" => //; last by case: (TInv t) invt.
  iDestruct "dec" as (T) "[%dec ?]".
  case: dec invt; try by move =>> // _ ->.
  move => t' -> _ _ /TInv_inj -> _. by iApply big_sepS_singleton.
- iIntros; iSplit; first by iApply public_minted.
  iLeft; iExists {[t]}; iSplit.
  + by iPureIntro; econstructor.
  + by iApply big_sepS_singleton.
Qed.

Lemma public_TExpN t ts :
  ¬ is_exp t →
  invs_canceled ts ->
  ts ≠ [] →
  public (TExpN t ts) ⊣⊢
  (∃ t' ts', ⌜ts ≡ₚ t' :: ts'⌝ ∧ public (TExpN t ts') ∧ public t') ∨
  minted (TExpN t ts) ∧
  [∗ list] t' ∈ ts,
    dh_pred t' (TExpN t ts) ∧ □ (public t' → public (TExp (TExpN t ts) (TInv t'))).
Proof.
move => /[dup] ? /negb_True /is_trueP ?.
move => /[dup] ? /is_trueP ?.
move => tsN0.

have ttsX: is_exp (TExpN t ts) by rewrite is_exp_TExpN; first case: (ts) tsN0.

apply: anti_symm.
- rewrite public_eq minted_TExpN // exps_TExpN' //.
  iIntros "#[[mt mts] [publ | [(_ & ?) | ?]]]"; [| by eauto | by case: (TExpN t ts) ttsX].
  iDestruct "publ" as (T) "[%dec publ]".
  move e: (TExpN t ts) => t' in dec ttsX *.
  case: dec ttsX; try by move=> * {e}; subst t'.
    by move => ? _ ? _ -> /is_trueP /(ssrbool.contraLR (is_exp_TInv _)) /is_trueP.
  rewrite -{}e {t'}.
  move=> t1 t2 -> /invs_canceled_cons_exps ? ? e ?.
  rewrite big_sepS_union_pers !big_sepS_singleton.
  iDestruct "publ" as "[publ1 publ2]".
  iLeft. iExists t2, (exps t1).
  have -> : TExpN t (exps t1) = t1.
    apply: base_exps_inj.
    + by move/(f_equal base): e; rewrite !base_TExpN.
    + rewrite exps_TExpN' //; exact: invs_canceled_exps.
  do !iSplit => //.
  by rewrite -(exps_TExpN' t ts) // e exps_TExpN -Permutation_cons_append cancel_exps_canceled.

- iIntros "#[publ | [m dhp]]".
  + iDestruct "publ" as (t' ts') "[%e [pts' pt']]".
    have canceled_t'ts': invs_canceled (t' :: ts') by rewrite -e.
    move: (canceled_t'ts'); rewrite invs_canceled_cons; case => ??.
    rewrite e in ttsX *.
    rewrite [public (TExpN _ (_ :: _))]public_eq minted_TExpN //=.
    iSplit.
      rewrite !public_minted minted_TExpN //=.
      by iDestruct "pts'" as "[??]"; eauto.
    iLeft; iExists {[TExpN t ts'; t']}.
    rewrite big_sepS_union_pers !big_sepS_singleton; do !iSplit => //.
    iPureIntro; apply: DExp; eauto.
      by rewrite exps_TExpN'.
      by rewrite TExp_TExpN.
  + by rewrite public_eq (exps_TExpN' t ts); eauto.
Qed.

Lemma public_TExpN' t :
  is_exp t ->
  public t ⊣⊢
  (∃ t', ⌜t' ∈ exps t⌝ ∧ public (TExp t (TInv t')) ∧ public t') ∨
  minted t ∧
  [∗ list] t' ∈ exps t,
    dh_pred t' t ∧ □ (public t' → public (TExp t (TInv t'))).
Proof.
move => expt; apply: anti_symm; rewrite public_eq.
- iIntros "(? & [publ | [(_ & ?) | ?]])"; [| by eauto | by case: t expt].
  iDestruct "publ" as (T) "[%dec publ]".
  case: dec expt; try by move =>> _ ->.
    by move => t' _ /is_trueP ? _ -> /is_trueP /(ssrbool.contraLR (is_exp_TInv t')).
  move => t1 t2 -> /invs_canceled_cons_exps ? _ -> _.
  rewrite big_sepS_union_pers !big_sepS_singleton.
  iLeft; iExists t2.
  rewrite TExpNK exps_TExpN -Permutation_cons_append cancel_exps_canceled // elem_of_cons.
  by eauto.
- iIntros "#[[%t' [%t'_in (? & ?)]] | (? & ?)]"; [iSplit | by eauto].
  + rewrite !public_minted -{2}(TExpK' t t'). iApply all_minted_TExpN; iSplit => //.
    by rewrite big_sepL_singleton.
  + iLeft; iExists {[ TExp t (TInv t'); t' ]}; iSplit.
    * iPureIntro; econstructor => //; last by rewrite TExpK'.
      rewrite -!count_exp_gt0 count_exp_TExp_eq count_exp_TInv in t'_in *. lia.
    * by rewrite big_sepS_union_pers !big_sepS_singleton; iSplit.
Qed.

Lemma public_TExp_iff t1 t2 :
  ¬ is_exp t1 →
  public (TExp t1 t2) ⊣⊢
  public t1 ∧ public t2 ∨
  minted t1 ∧ minted t2 ∧ dh_pred t2 (TExp t1 t2) ∧ □ (public t2 → public t1).
Proof.
move=> ?; rewrite public_TExpN //=; last exact: invs_canceled1.
rewrite TExpNK.
apply: (anti_symm _); iIntros "#pub".
- iDestruct "pub" as "[pub | pub]" => //.
  + iDestruct "pub" as (??) "(%e & p_t1 & p_t2)".
    case/Permutation_singleton_l: e => -> <-.
    by rewrite TExpN0; eauto.
  + by rewrite minted_TExp //; iDestruct "pub" as "[[??] [[??] _]]"; eauto.
- iDestruct "pub" as "[[p1 p2] | (s1 & s2 & ? & ?)]".
  + by iLeft; iExists t2, []; rewrite TExpN0; eauto.
  + by rewrite minted_TExp; eauto 6.
Qed.

Lemma public_TExp2_iff t1 t2 t3 :
  ¬ is_exp t1 →
  t2 ≠ TInv t3 ->
  public (TExpN t1 [t2; t3]) ⊣⊢
  public (TExpN t1 [t2]) ∧ public t3 ∨
  public (TExpN t1 [t3]) ∧ public t2 ∨
  minted (TExpN t1 [t2; t3]) ∧
  dh_pred t2 (TExpN t1 [t2; t3]) ∧
  dh_pred t3 (TExpN t1 [t2; t3]) ∧
  □ (public t2 → public (TExp t1 t3)) ∧
  □ (public t3 → public (TExp t1 t2)).
Proof.
move => ? /invs_canceled2 ?; rewrite public_TExpN //=.
apply: anti_symm; iIntros "#pub".
- iDestruct "pub" as "[pub | (? & [??] & [??] & _)]".
  + iDestruct "pub" as (??) "(%e & p_t1 & p_t2)".
    by case: (Permutation_length_2_inv e) => [[-> ->] | [-> ->]]; eauto.
  + by rewrite -TExp_TExpN TExpNK TExpNC TExpNK; eauto 7.
- iDestruct "pub" as "[[? ?] | [[? ?] | (? & ? & ? & ? & ?)]]".
  + by setoid_rewrite perm_swap at 1; eauto 6.
  + by eauto 8.
  + by rewrite -TExp_TExpN TExpNK TExpNC TExpNK; eauto 7.
Qed.

Lemma public_TExp t1 t2 :
  public t1 -∗
  public t2 -∗
  public (TExp t1 t2).
Proof.
have H : ∀ t1 t2, TInv t2 ∉ exps t1 →
    public t1 -∗ public t2 -∗ public (TExp t1 t2).
  move=> {}t1 {}t2 /invs_canceled_cons_exps in_exps.
  iIntros "#p1 #p2".
  rewrite -{2}(base_expsK t1) TExp_TExpN public_TExpN //.
  by iLeft; iExists t2, (exps t1); rewrite base_expsK; eauto.
case: (decide (TInv t2 ∈ exps t1)) => in_exps; last exact: H.
elim /term_lt_ind: t1 in_exps => t1 IH in_exps.
have [exp_t1|contra] := decide (is_exp t1); last first.
  by rewrite exps_expN // elem_of_nil in in_exps.
iIntros "#p1 #p2"; rewrite [public t1]public_TExpN' //.
iDestruct "p1" as "[(%t3 & %t3_t1 & p1' & p3) | [m1 p1]]"; last first.
  rewrite big_sepL_elem_of // TInvK public_TInv. by iApply "p1".
have t2_t3: t2 ≠ t3 by apply elem_of_TInv_exps' in in_exps; congruence.
case: (decide (t2 = TInv t3)) => [-> | t2_t3V] //.
set t1' := TExp t1 (TInv t3).
have eq: TExp (TExp t1' t2) t3 = TExp t1 t2 by rewrite TExpNC TExpK'.
have in_exps': TInv t2 ∈ exps t1'.
  rewrite -count_exp_gt0 count_exp_TInv /t1' count_exp_TExp_ne ?TInvK //.
  by rewrite -count_exp_TInv count_exp_gt0.
iAssert (public (TExp t1' t2)) as "p1''".
  by iApply IH; first apply tsize_TExp_TInv.
rewrite -eq; iApply H => //.
rewrite -count_exp_gt0 count_exp_TInv count_exp_TExp_ne //; last first.
  by move => e; rewrite e TInvK in t2_t3V.
rewrite count_exp_TExp_TInv; rewrite -count_exp_gt0 in t3_t1; lia.
Qed.

Lemma dh_pred_exps t1 t2 :
  t2 ∈ exps t1 ->
  public t1 -∗
  dh_pred t2 t1 ∧ □ (public t2 → public (TExp t1 (TInv t2))).
Proof.
elim /term_lt_ind: t1 => t1 IH.
have [exp_t1|contra] := decide (is_exp t1); last first.
  by rewrite exps_expN // elem_of_nil.
move => t2_t1. iIntros "#p".
rewrite public_TExpN' // big_sepL_elem_of //.
iDestruct "p" as "[p | [_ [dh ?]]]" => //; eauto.
iDestruct "p" as (t t_t1) "[p1 pt]".
case: (decide (t2 = t)) => [-> | t2_t].
  by iSplit; eauto; iApply dh_pred_intro3.
have t2_tV : t2 ≠ TInv t.
  by move=> e; rewrite e -!count_exp_gt0 count_exp_TInv in t_t1 t2_t1; lia.
rewrite -{2}(TExpK' t1 t); set t1' := TExp t1 (TInv t).
have size_lt: tsize t1' < tsize t1 by apply tsize_TExp_TInv.
have t2_t1': t2 ∈ exps t1'.
  by rewrite -count_exp_gt0 count_exp_TExp_ne // ?TInvK // count_exp_gt0.
iPoseProof (IH _ size_lt t2_t1' with "p1") as "[dh #p]"; iSplit.
- iApply dh_pred_intro2 => //.
  + by rewrite not_elem_of_TInv_exps /t1' TExpK'.
  + by iApply dh_pred_intro3.
- iIntros "!> #p2".
  rewrite -[in public (TExp t1 (TInv t2))](TExpK' t1 t).
  rewrite TExpNC; iApply public_TExp => //.
  by iApply "p".
Qed.

Lemma False_public t :
  minted t -∗
  ▷ False -∗
  public t.
Proof.
elim: t.
- iIntros "%n _ _".
  by rewrite public_TInt.
- iIntros "%t1 %IH1 %t2 %IH2".
  rewrite minted_TPair public_TPair.
  iIntros "#[m1 m2] #contra"; iSplit.
  + by iApply IH1.
  + by iApply IH2.
- iIntros "%a #m #contra".
  rewrite minted_TNonce public_TNonce; iSplit => //.
  iDestruct "contra" as ">[]".
- iIntros "%k %t %IH #m #contra".
  by rewrite minted_TKey public_TKey; iLeft; iApply IH.
- iIntros "%k %IHk %t %IHt".
  rewrite minted_TSeal public_TSeal.
  iIntros "#[m1 m2] #contra". iLeft; iSplit.
  + by iApply IHk.
  + by iApply IHt.
- iIntros "%t %IH #m #contra".
  by rewrite minted_THash public_THash; iLeft; iApply IH.
- iIntros "%t %IH _ #m #contra".
  by rewrite minted_TInv public_TInv; iApply IH.
- move => t IHt nX ts IHts nZ _ canceled.
  apply is_trueP in canceled.
  apply is_trueP in nX; apply negb_True in nX.
  apply (ssrbool.elimN eqtype.eqP) in nZ.

  elim: ts nZ IHts canceled => //= t' ts' IHts _ [Ht' Hts'] canceled.
  move: (canceled); rewrite invs_canceled_cons; move => [_ ?].
  rewrite minted_TExpN //=.
  iIntros "#[mt [mt' mts']] #contra".

  case eqn: (ts'); first by iApply public_TExp; [iApply IHt | iApply Ht'].

  rewrite -eqn public_TExpN //.
  iLeft; iExists t', ts'; do !iSplit => //; last by iApply Ht'.
  iApply IHts => //.
  + by rewrite eqn.
  + by rewrite minted_TExpN //; iSplit.
Qed.

Lemma public_TExp' t1 t2 :
  TInv t2 ∉ exps t1 →
  public t1 -∗
  minted t2 -∗
  dh_pred t2 (TExp t1 t2) -∗
  public (TExp t1 t2).
Proof.
elim/term_lt_ind: t1 => t1 IH in t2 *.
iIntros "%t2_t1 #p1 #m #dh".
rewrite [public (TExp _ _)]public_TExpN' //; last first.
  case: (decide (is_exp (TExp t1 t2))) => [//|nX].
  by rewrite not_elem_of_TInv_exps exps_expN // elem_of_nil in t2_t1.
iRight; iSplit.
  by rewrite public_minted; iApply all_minted_TExp; iSplit.
iApply big_sepL_forall; iIntros (k t t_t1').
have {}t_t1': t ∈ exps (TExp t1 t2) by apply: elem_of_list_lookup_2.
have [->|t_t2] := decide (t = t2).
  by iSplit => //; iIntros "!> #p2"; rewrite TExpNK.
have t_t1: t ∈ exps t1.
  rewrite -!count_exp_gt0 count_exp_TExp decide_False // in t_t1' *.
  case: decide => ? in t_t1'; lia.
iPoseProof (dh_pred_exps t_t1 with "p1") as "[dh_t #p1']".
iSplit; first by iApply dh_pred_intro2.
iIntros "!> #p"; iSpecialize ("p1'" with "p").


  iDestruct "p" as "(%t & %t_t1 & p_t1' & p_t)".
  rewrite -[X in public (TExp X t2)](TExpNK' [t]) /=.
  rewrite (TExpNC _ [t]); iApply public_TExp => //.

rewrite -{3}(base_expsK t1) TExp_TExpN public_TExpN //; last exact /invs_canceled_cons_exps.
rewrite -(TExp_TExpN (base _)) base_expsK.

iRight; do !iSplit => //=.
-
- by rewrite TExpNK; eauto.
- rewrite big_sepL_forall. iIntros (k t' t'_in); apply elem_of_list_lookup_2 in t'_in.
  iSplit.
  + by iApply dh_pred_intro2 => //; first iApply dh_pred_exps.
  + iIntros "!> #pt'".
    case: (decide (t2 = t')) => [-> | ?]; first by rewrite TExpNK.
    case: (decide (t2 = TInv t')) => [-> | ?].
      by do !iApply public_TExp; rewrite ?public_TInv.
    rewrite TExpNC. iApply IH => //.
    * by apply tsize_TExp_TInv.
    * rewrite -count_exp_gt0 count_exp_TInv count_exp_TExp_ne ?TInvK //.
      by rewrite -count_exp_TInv count_exp_gt0.
    * by iApply public_TExp; last rewrite public_TInv.
    * rewrite TExpNC; iApply dh_pred_intro2 => //.
      by iApply dh_pred_intro3; rewrite public_TInv.
Qed.

Lemma public_TExp'' t1 t2 :
  public t1 -∗
  minted t2 -∗
  dh_pred t2 (TExp t1 t2) -∗
  □ (∀ t, dh_pred_base (TInv t2) t ↔ ▷ False) -∗
  ▷ public (TExp t1 t2).
Proof.
case: (decide (TInv t2 ∈ exps t1)) => in_exps; last first.
  iIntros "#p1 #m2 #dh #dhV".
  by iApply public_TExp'.
iIntros "#p1 #m2 #dh #dhV".
iPoseProof (dh_pred_exps in_exps with "p1") as "dh'".
iPoseProof (dh_pred_inv_same in_exps with "dh'") as "[p2|H]".
  by rewrite public_TInv; iApply public_TExp.
iDestruct "H" as "(%t2' & _ & _ & contra)".
by iDestruct ("dhV" with "contra") as ">[]".
Qed.

Lemma public_to_list t ts :
  Spec.to_list t = Some ts →
  public t -∗ [∗ list] t' ∈ ts, public t'.
Proof.
elim/term_ind': t ts => //=.
  by case=> // ts [<-] /=; iIntros "?".
move=> t _ tl IH ts.
case e: (Spec.to_list tl) => [ts'|] // [<-] /=.
rewrite public_TPair /=; iIntros "[??]"; iFrame.
by iApply IH.
Qed.

Lemma public_of_list ts :
  public (Spec.of_list ts) ⊣⊢
  [∗ list] t ∈ ts, public t.
Proof.
rewrite Spec.of_list_unseal.
elim: ts => [|t ts IH]; first by rewrite public_TInt.
by rewrite public_TPair /= IH bi.persistent_and_sep.
Qed.

Lemma public_Tag N : public (Tag N) ⊣⊢ True.
Proof. by rewrite Tag_unseal public_TInt. Qed.

Lemma public_tag N t : public (Spec.tag (Tag N) t) ⊣⊢ public t.
Proof.
by rewrite Spec.tag_unseal public_TPair public_Tag bi.emp_and.
Qed.

Lemma public_TSeal_tag k N t :
  public (TSeal k (Spec.tag (Tag N) t)) ⊣⊢
  public k ∧ public t ∨
  minted k ∧ minted t ∧
  match func_of_term k with
  | Some F => ∃ Φ,
      ⌜Spec.is_seal_key k⌝ ∧
      seal_pred F N Φ ∧
      □ ▷ Φ (Spec.skey k) t ∧
      match Spec.open_key k with
      | Some k' => □ (public k' → public t)
      | None => True
      end
  | None => True
  end.
Proof.
rewrite public_TSeal {1}public_tag minted_TSeal minted_tag.
rewrite [(_ ∧ _ ∧ _)%I]assoc.
apply: bi.or_proper => //.
apply: bi.and_proper => //.
case: func_of_term => // F.
apply (anti_symm _).
- iIntros "(? & (%N' & %t' & %Φ & %e & ? & ?) & ?)".
  case/Spec.tag_inj: e => [/Tag_inj <- <-].
  iExists Φ. do !iSplit => //.
  case: Spec.open_key => // k'. by rewrite public_tag.
- iIntros "(%Φ & ? & ? & ? & ?)".
  do !iSplit => //.
  + iExists N, t, Φ. by eauto.
  + case: Spec.open_key => // k'. by rewrite public_tag.
Qed.

Lemma public_TSealE N Φ k t F :
  public (TSeal k (Spec.tag (Tag N) t)) -∗
  ⌜func_of_term k = Some F ∧ Spec.is_seal_key k⌝ -∗
  seal_pred F N Φ -∗
  public k ∧ public t ∨
  □ ▷ Φ (Spec.skey k) t ∧
  match Spec.open_key k with
  | Some k' => □ (public k' → public t)
  | None => True
  end.
Proof.
iIntros "#Ht %kP #HΦ"; rewrite public_TSeal; case: kP => [-> k_seal].
iDestruct "Ht" as "[[? Ht] | [_ Ht]]"; first by rewrite public_tag; eauto.
iDestruct "Ht" as "(_ & inv & ?)".
iPoseProof (wf_seal_elim with "inv HΦ") as "?".
iRight. iSplit => //. case: Spec.open_key => // ?.
by rewrite public_tag.
Qed.

Lemma public_TSealIS F N Φ k t :
  ⌜func_of_term k = Some F ∧ Spec.is_seal_key k⌝ -∗
  seal_pred F N Φ -∗
  □ Φ (Spec.skey k) t -∗
  minted k -∗
  minted t -∗
  match Spec.open_key k with
  | Some k' => □ (public k' → public t)
  | None => True
  end -∗
  public (TSeal k (Spec.tag (Tag N) t)).
Proof.
iIntros "[%k_F %kP] #HΦ #HΦt #m_k #m_t #Hopenl".
rewrite public_TSeal k_F. iRight. rewrite minted_TSeal minted_tag.
iSplit; first by eauto. iSplit => //. iSplit; last first.
{ case: Spec.open_key => // ?. by rewrite public_tag. }
iExists N, t, Φ. eauto.
Qed.

Lemma public_TSealIP k t :
  public k -∗
  public t -∗
  public (TSeal k t).
Proof. by iIntros "? ?"; rewrite public_TSeal; eauto. Qed.

Lemma nonce_alloc P Q a :
  meta_token a ⊤ -∗
  (minted (TNonce a) -∗ False) ∧
  |==> minted (TNonce a) ∗
    □ (public (TNonce a) ↔ ▷ □ P (TNonce a)) ∗
    □ (∀ t, dh_pred_base (TNonce a) t ↔ ▷ □ Q t).
Proof.
iIntros "token".
iSplit.
{ rewrite minted_TNonce. iIntros "contra".
  by iDestruct (meta_meta_token with "token contra") as "[]". }
iMod (own_alloc (saved_pred DfracDiscarded P)) as (γP) "#own_P" => //.
iMod (own_alloc (saved_pred DfracDiscarded Q)) as (γQ) "#own_Q" => //.
rewrite (meta_token_difference a (↑nroot.@"nonce")) //.
iDestruct "token" as "[nonce token]".
iMod (meta_set _ _ γP with "nonce") as "#nonce"; eauto.
rewrite (meta_token_difference a (↑nroot.@"dh")); last solve_ndisj.
iDestruct "token" as "[dh token]".
iMod (meta_set _ _ γQ with "dh") as "#dh"; eauto.
rewrite (meta_token_difference a (↑nroot.@"minted")); last solve_ndisj.
iDestruct "token" as "[minted token]".
iMod (meta_set _ _ () (nroot.@"minted") with "minted") as "#minted" => //.
iSplitR.
  by rewrite minted_TNonce.
iSplitR.
  rewrite public_TNonce; do 2!iModIntro; iSplit.
  + iIntros "[#public _]".
    iDestruct "public" as (γP' P') ">(#meta_γP' & #own_P' & ?)".
    iPoseProof (meta_agree with "nonce meta_γP'") as "->".
    iPoseProof (own_valid_2 with "own_P own_P'") as "valid".
    iPoseProof (saved_pred_op_validI with "valid") as "[_ #e]".
    iSpecialize ("e" $! (TNonce a)). iModIntro. by iRewrite "e".
  + iIntros "#?". iSplit => //. iExists γP, P; eauto.
iIntros "!> !> %t"; iSplit.
- iDestruct 1 as (γQ' Q') "(#meta_γQ' & #own_Q' & ?)".
  iPoseProof (meta_agree with "dh meta_γQ'") as "->".
  iPoseProof (own_valid_2 with "own_Q own_Q'") as "valid".
  iPoseProof (saved_pred_op_validI with "valid") as "[_ #e]".
  iSpecialize ("e" $! t). iModIntro. by iRewrite "e".
- by iIntros "#?"; iExists _, _; eauto.
Qed.

Lemma public_pkey k : public k ⊢ public (Spec.pkey k).
Proof.
iIntros "#p_k".
iPoseProof (public_minted with "p_k") as "m_k".
case: k => // - [] // t; iClear "p_k";
rewrite minted_TKey public_TKey /=; eauto.
Qed.

Lemma public_senc_key k : public (SEncKey k) ⊣⊢ public k.
Proof.
rewrite [term_of_senc_key]unlock public_TKey /=.
iSplit; eauto.
by iIntros "[#p_k|[? []]]"; eauto.
Qed.

Lemma public_senc_key' (sk : senc_key) :
  public sk ⊣⊢ public (seed_of_senc_key sk).
Proof.
case: sk => seed. by rewrite public_senc_key.
Qed.

Lemma public_aenc_key (sk : aenc_key) : public (Spec.pkey sk) ⊣⊢ minted sk.
Proof.
rewrite [term_of_aenc_key]unlock; case: sk => [seed] /=.
rewrite public_TKey /= minted_TKey. iSplit; eauto.
iIntros "[#p_k|[? ?]]"; eauto.
by iApply public_minted.
Qed.

Lemma public_adec_key k : public (AEncKey k) ⊣⊢ public k.
Proof.
rewrite [term_of_aenc_key]unlock public_TKey /=.
iSplit; eauto.
by iIntros "[#p_k|[? []]]"; eauto.
Qed.

Lemma public_adec_key' (sk : aenc_key) :
  public sk ⊣⊢ public (seed_of_aenc_key sk).
Proof. case: sk => seed. by rewrite public_adec_key. Qed.

Lemma public_verify_key (sk : sign_key) : public (Spec.pkey sk) ⊣⊢ minted sk.
Proof.
rewrite [term_of_sign_key]unlock; case: sk => seed /=. rewrite public_TKey /= minted_TKey.
iSplit; eauto.
iIntros "[#p_k|[? ?]]"; eauto.
by iApply public_minted.
Qed.

Lemma public_sign_key k : public (SignKey k) ⊣⊢ public k.
Proof.
rewrite [term_of_sign_key]unlock public_TKey /=.
iSplit; eauto.
by iIntros "[#p_k|[? []]]"; eauto.
Qed.

Lemma public_sign_key' (sk : sign_key) :
  public sk ⊣⊢ public (seed_of_sign_key sk).
Proof.
case: sk => seed. by rewrite public_sign_key.
Qed.

Definition pending γ : iProp :=
  gmeta_token γ ⊤.

Definition shot γ (x : positive) : iProp :=
  gmeta γ nroot x.

Global Instance persistent_shot γ x : Persistent (shot γ x).
Proof. apply _. Qed.

Global Instance timeless_shot γ x : Timeless (shot γ x).
Proof. apply _. Qed.

Lemma pending_alloc : ⊢ |==> ∃ γ, pending γ.
Proof. apply gmeta_token_alloc. Qed.

Lemma shot_alloc γ x : pending γ ==∗ shot γ x.
Proof. by apply gmeta_set. Qed.

Lemma pending_shot γ x : pending γ -∗ shot γ x -∗ False.
Proof. by apply gmeta_gmeta_token. Qed.

Lemma shot_agree γ x y : shot γ x -∗ shot γ y -∗ ⌜x = y⌝.
Proof. apply gmeta_agree. Qed.

Definition secret t : iProp :=
  (|==> public t) ∧
  (|==> □ (public t ↔ ▷ False)) ∧
  (public t -∗ ▷ False).

Lemma secret_alloc t γ :
  □ (public t ↔ ▷ shot γ 1) -∗ pending γ -∗ secret t.
Proof.
iIntros "#s_t pending"; do 2?iSplit.
- iMod (shot_alloc with "pending") as "#shot".
  by iSpecialize ("s_t" with "shot").
- iMod (shot_alloc _ 2 with "pending") as "#shot".
  iIntros "!> !>". iSplit.
  + iIntros "#p_t".
    iPoseProof ("s_t" with "p_t") as ">#shot'".
    by iPoseProof (shot_agree with "shot shot'") as "%".
  + iIntros "#contra".
    iApply "s_t". by iDestruct "contra" as ">[]".
- iIntros "#p_t".
  iPoseProof ("s_t" with "p_t") as ">#shot".
  by iPoseProof (pending_shot with "[$] [//]") as "[]".
Qed.

Lemma secret_not_public t : secret t -∗ public t -∗ ▷ False.
Proof. by iIntros "(_ & _ & contra)". Qed.

Lemma secret_public t : secret t ==∗ public t.
Proof. by iIntros "(? & _)". Qed.

Lemma freeze_secret t : secret t ==∗ □ (public t ↔ ▷ False).
Proof. by iIntros "(_ & ? & _)". Qed.

Lemma public_aencIS (sk : aenc_key) N Φ t :
  aenc_pred N Φ -∗
  minted sk -∗
  minted t -∗
  □ Φ sk t -∗
  □ (public sk → public t) -∗
  public (TSeal (Spec.pkey sk) (Spec.tag (Tag N) t)).
Proof.
rewrite [term_of_aenc_key]unlock; case: sk => seed /=.
rewrite minted_TKey. iIntros "#? #m_k #m_t #inv #p_t".
iApply public_TSealIS => //.
- iModIntro. iExists (AEncKey _). rewrite [term_of_aenc_key]unlock. by eauto.
- by rewrite minted_TKey.
Qed.

Lemma public_sencIS (k : senc_key) N Φ t :
  senc_pred N Φ -∗
  minted k -∗
  minted t -∗
  □ Φ k t -∗
  □ (public k → public t) -∗
  public (TSeal k (Spec.tag (Tag N) t)).
Proof.
rewrite [term_of_senc_key]unlock; case: k => seed /=.
iIntros "#? #m_k #m_t #inv #p_t".
iApply public_TSealIS => //.
iModIntro. iExists (SEncKey _). rewrite [term_of_senc_key]unlock. by eauto.
Qed.

Lemma public_signIS (sk : sign_key) N Φ t :
  sign_pred N Φ -∗
  minted sk -∗
  public t -∗
  □ Φ sk t -∗
  public (TSeal sk (Spec.tag (Tag N) t)).
Proof.
rewrite [term_of_sign_key]unlock; case: sk => seed /=.
rewrite minted_TKey.
iIntros "#? #m_k #p_t #inv".
iApply public_TSealIS => //.
- iModIntro. iExists (SignKey _). rewrite [term_of_sign_key]unlock; by eauto.
- by rewrite minted_TKey.
- by iApply public_minted.
- by iIntros "!> _".
Qed.

Lemma public_aencE (sk : aenc_key) N Φ t :
  public (TSeal (Spec.pkey sk) (Spec.tag (Tag N) t)) -∗
  aenc_pred N Φ -∗
  minted t ∧ (public t ∨ □ ▷ Φ sk t ∧ □ (public sk → public t)).
Proof.
rewrite keysE; case: sk => seed /=.
iIntros "#p_t #?". iSplit => //.
{ iPoseProof (public_minted with "p_t") as "#m_t".
  rewrite minted_TSeal minted_tag. by iDestruct "m_t" as "[_ ?]". }
iPoseProof (public_TSealE with "p_t [//] [//]") as "[[_ comp]|inv]"; eauto.
rewrite /=. iDestruct "inv" as "[#inv #?]". iRight. iSplit => //.
iIntros "!> !>". iDestruct "inv" as "(%k' & %e & inv)".
rewrite keysE in e. by case: k' e => seed' // [<-].
Qed.

Lemma public_signE (sk : sign_key) N Φ t :
  public (TSeal sk (Spec.tag (Tag N) t)) -∗
  sign_pred N Φ -∗
  public t ∧ (public sk ∨ □ ▷ Φ sk t).
Proof.
rewrite keysE; case: sk => seed /=.
iIntros "#p_t #?". iPoseProof (public_minted with "p_t") as "m_t".
rewrite minted_TSeal minted_TKey. iDestruct "m_t" as "[? _]".
iPoseProof (public_TSealE with "p_t [//] [//]") as "[[??]|inv]"; eauto.
iDestruct "inv" as "{p_t} (#inv & #p_t)". iSplit => //.
- iApply "p_t". iApply public_TKey. iRight. by iSplit => //.
- iRight. iIntros "!> !>". iDestruct "inv" as "(%k' & %e & inv)".
  rewrite keysE in e; by case: k' e => seed' // [<-].
Qed.

Lemma public_sencE (k : senc_key) N Φ t :
  public (TSeal k (Spec.tag (Tag N) t)) -∗
  senc_pred N Φ -∗
  minted t ∧ (public k ∨ □ ▷ Φ k t) ∧ □ (public k → public t).
Proof.
rewrite keysE; case: k => seed /=.
iIntros "#p_t #?". iSplit => //.
{ iPoseProof (public_minted with "p_t") as "#m_t".
  rewrite minted_TSeal minted_tag. by iDestruct "m_t" as "[_ ?]". }
iPoseProof (public_TSealE with "p_t [//] [//]") as "[[??]|[#inv #p_t']]";
eauto. iSplit => //. iRight.
iIntros "!> !>". iDestruct "inv" as "(%k' & %e & inv)".
rewrite keysE in e; by case: k' e => seed' // [<-].
Qed.
End Public.

Arguments public_aenc_name {Σ _}.
Arguments public_sign_name {Σ _}.
Arguments public_senc_name {Σ _}.
Arguments seal_pred {Σ _} F N Φ.
Arguments seal_pred_set {Σ _} F {_} N Φ.
Arguments seal_pred_token_difference {Σ _} F E1 E2.
Arguments public_hash_name {Σ _}.
Arguments hash_pred {Σ _} N P.
Arguments hash_pred_set {Σ _ _} N P.
Arguments hash_pred_token_difference {Σ _} E1 E2.

Lemma publicGS_alloc `{!heapGS Σ} E :
  publicGpreS Σ →
  ⊢ |={E}=> ∃ (H : publicGS Σ),
             seal_pred_token AENC ⊤ ∗
             seal_pred_token SIGN ⊤ ∗
             seal_pred_token SENC ⊤ ∗
             hash_pred_token ⊤.
Proof.
move=> ?; iStartProof.
iMod gmeta_token_alloc as (γ_aenc) "own_aenc".
iMod gmeta_token_alloc as (γ_sign) "own_sign".
iMod gmeta_token_alloc as (γ_senc) "own_senc".
iMod gmeta_token_alloc as (γ_hash) "own_hash".
pose (H := PublicGS _ γ_aenc γ_sign γ_senc γ_hash).
iExists H. by iFrame.
Qed.
