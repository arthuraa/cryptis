From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap list reservation_map excl.
From iris.algebra Require Import functions.
From iris.base_logic.lib Require Import saved_prop invariants.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib gmeta nown.
From cryptis.core Require Import term comp_map minted.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition term_namesUR := authUR (gmapUR term (agreeR gnameO)).

Class term_metaGpreS Σ : Type := TermMetaGPreS {
  term_meta_meta : metaGS Σ;
  term_meta_names : inG Σ term_namesUR;
}.

Local Existing Instance term_meta_meta.
Local Existing Instance term_meta_names.

Class term_metaGS Σ : Type := TermMetaGS {
  term_meta_inG  : term_metaGpreS Σ;
  term_meta_name : gname;
}.

Global Existing Instance term_meta_inG.

Definition term_metaΣ : gFunctors :=
  #[metaΣ; GFunctor term_namesUR].

Global Instance subG_term_metaGpreS Σ :
  subG term_metaΣ Σ → term_metaGpreS Σ.
Proof. solve_inG. Qed.

Section TermMeta.

Context `{!heapGS Σ}.
Notation iProp := (iProp Σ).
Notation iPropO := (iPropO Σ).
Notation iPropI := (iPropI Σ).

Definition term_meta_inv `{!term_metaGS Σ} : iProp :=
  ∃ names : gmap term gname,
    own term_meta_name (● ((to_agree <$> names) : gmap _ _)) ∗
    [∗ set] t ∈ dom names, minted t.

Definition term_meta_ctx `{!term_metaGS Σ} : iProp :=
  inv (nroot.@"cryptis".@"meta") term_meta_inv.

Lemma term_metaGS_alloc E :
  term_metaGpreS Σ →
  ⊢ |={E}=> ∃ (H : term_metaGS Σ), term_meta_ctx.
Proof.
move=> ?; iStartProof.
iMod (own_alloc (● (∅ : gmap term (agree gname)))) as (γ_names) "names_auth".
  by apply auth_auth_valid.
pose (H := TermMetaGS _ γ_names).
iExists H. iApply inv_alloc.
iExists ∅. rewrite fmap_empty /=. iFrame.
by rewrite dom_empty_L big_sepS_empty.
Qed.

Context `{!term_metaGS Σ}.

Global Instance term_meta_inv_timeless : Timeless term_meta_inv.
Proof. rewrite /term_meta_inv. apply _. Qed.

#[global]
Instance term_meta_ctx_persistent : Persistent term_meta_ctx.
Proof. apply _. Qed.

Class HasTermMetaCtx (ctx : iProp) := {
  has_term_meta_ctx : ctx ⊢ term_meta_ctx;
  has_term_meta_ctx_persistent : Persistent ctx;
}.

Local Existing Instance has_term_meta_ctx_persistent.

Context `{!HasTermMetaCtx ctx}.

Definition term_name t γ : iProp :=
  own term_meta_name (◯ {[t := to_agree γ]}).

Global Instance term_name_persistent t γ : Persistent (term_name t γ).
Proof. apply _. Qed.

Global Instance term_name_timeless t γ : Timeless (term_name t γ).
Proof. apply _. Qed.

Lemma term_name_agree t γ1 γ2 :
  term_name t γ1 -∗
  term_name t γ2 -∗
  ⌜γ1 = γ2⌝.
Proof.
iIntros "name1 name2".
iPoseProof (own_valid_2 with "name1 name2") as "%valid".
rewrite -auth_frag_op auth_frag_valid in valid.
move/(_ t): valid.
rewrite lookup_op !lookup_singleton -Some_op Some_valid.
by move=> /to_agree_op_inv_L ->.
Qed.

Definition term_token_def t E : iProp :=
  ∃ γ, term_name t γ ∗ gmeta_token γ E.
Definition term_token_aux : seal term_token_def. by eexists. Qed.
Definition term_token := unseal term_token_aux.
Lemma term_token_unseal : term_token = term_token_def.
Proof. exact: seal_eq. Qed.

Definition term_meta_def `{Countable L} t N (x : L) : iProp :=
  ∃ γ, term_name t γ ∗ gmeta γ N x.
Definition term_meta_aux : seal (@term_meta_def). by eexists. Qed.
Definition term_meta := unseal term_meta_aux.
Lemma term_meta_unseal : @term_meta = @term_meta_def.
Proof. exact: seal_eq. Qed.
Arguments term_meta {L _ _} t N x.

Global Instance term_token_timeless t E : Timeless (term_token t E).
Proof. rewrite term_token_unseal. apply _. Qed.

Global Instance term_meta_timeless `{Countable L} t N (x : L) :
  Timeless (term_meta t N x).
Proof. rewrite term_meta_unseal. apply _. Qed.

Global Instance term_meta_persistent `{Countable L} t N (x : L) :
  Persistent (term_meta t N x).
Proof. rewrite term_meta_unseal. apply _. Qed.

Lemma term_token_drop E1 E2 t :
  E1 ⊆ E2 → term_token t E2 -∗ term_token t E1.
Proof.
rewrite term_token_unseal.
iIntros "% (%γ & #name & token)".
iExists γ. iSplit => //. by iApply gmeta_token_drop.
Qed.

Lemma term_token_disj E1 E2 t :
  term_token t E1 -∗ term_token t E2 -∗ ⌜E1 ## E2⌝.
Proof.
rewrite term_token_unseal.
iIntros "(% & #name1 & token1) (% & #name2 & token2)".
iPoseProof (term_name_agree with "name1 name2") as "<-".
iApply (gmeta_token_disj with "token1 token2").
Qed.

Lemma term_token_difference t E1 E2 :
  E1 ⊆ E2 → term_token t E2 ⊣⊢ term_token t E1 ∗ term_token t (E2 ∖ E1).
Proof.
rewrite term_token_unseal.
move=> sub. iSplit.
- iIntros "(% & #name & token)".
  rewrite (gmeta_token_difference _ _ _ sub).
  iDestruct "token" as "[token1 token2]".
  by iSplitL "token1"; iExists _; iFrame.
- iIntros "[(% & #name1 & token1) (% & #name2 & token2)]".
  iPoseProof (term_name_agree with "name1 name2") as "<-".
  iExists _; iSplit => //.
  rewrite (gmeta_token_difference _ _ _ sub). by iFrame.
Qed.

Lemma term_meta_token `{Countable L} t (x : L) N E :
  ↑N ⊆ E → term_token t E -∗ term_meta t N x -∗ False.
Proof.
rewrite term_token_unseal term_meta_unseal => sub.
iIntros "(% & #name1 & token) (% & #name2 & #meta)".
iPoseProof (term_name_agree with "name1 name2") as "<-".
by iApply (gmeta_gmeta_token with "token meta").
Qed.

Lemma term_meta_set' `{Countable L} N (x : L) E t :
  ↑N ⊆ E → term_token t E ==∗ term_meta t N x ∗ term_token t (E ∖ ↑N).
Proof.
rewrite term_token_unseal term_meta_unseal.
iIntros "%sub (%γ & #name & token)".
iMod (gmeta_set' _ _ _ x sub with "token") as "[#meta token]".
iModIntro.
by iSplit; iExists _; iSplit => //.
Qed.

Lemma term_meta_set `{Countable L} N (x : L) E t :
  ↑N ⊆ E → term_token t E ==∗ term_meta t N x.
Proof.
iIntros "%sub token".
iMod (term_meta_set' x _ sub with "token") as "[#meta token]".
by iModIntro.
Qed.

Lemma term_meta_agree `{Countable L} t N (x1 x2 : L) :
  term_meta t N x1 -∗ term_meta t N x2 -∗ ⌜x1 = x2⌝.
Proof.
rewrite term_meta_unseal.
iIntros "(% & #name1 & #meta1) (% & #name2 & #meta2)".
iPoseProof (term_name_agree with "name1 name2") as "<-".
iApply (gmeta_agree with "meta1 meta2").
Qed.

Lemma term_token_switch t N' Q : ⊢ switch (term_token t (↑N')) Q.
Proof.
iExists (term_meta t N' ()). iSplit; iModIntro.
- iIntros "[token #meta]".
  by iDestruct (term_meta_token with "token meta") as "[]".
- iIntros "token".
  by iMod (term_meta_set () with "token") as "#meta".
Qed.

Section TermOwn.

Definition term_own_def `{inG Σ A} t N (x : A) : iProp :=
  ∃ γ, term_name t γ ∗ nown γ N x.
Definition term_own_aux : seal (@term_own_def). by eexists. Qed.
Definition term_own := unseal (@term_own_aux).
Lemma term_own_unseal : @term_own = @term_own_def.
Proof. exact: seal_eq. Qed.
Arguments term_own {A _} t N x.

Context `{inG Σ A}.

Lemma term_own_alloc t N {E} (a : A) :
  ↑N ⊆ E → ✓ a → term_token t E ==∗ term_own t N a ∗ term_token t (E ∖ ↑N).
Proof.
rewrite term_own_unseal term_token_unseal.
iIntros "%sub %val (% & #name & token)".
iMod (nown_alloc _ _ sub val with "token") as "[own token]".
iModIntro.
by iSplitL "own"; iExists _; iFrame.
Qed.

Lemma term_own_valid t N (a : A) : term_own t N a -∗ ✓ a.
Proof.
rewrite term_own_unseal.
iIntros "(%γ' & #own_γ & own)". iApply (nown_valid with "own").
Qed.

Lemma term_own_valid_2 t N (a1 a2 : A) :
  term_own t N a1 -∗ term_own t N a2 -∗ ✓ (a1 ⋅ a2).
Proof.
rewrite term_own_unseal.
iIntros "(%γ1 & #own_γ1 & own1) (%γ2 & #own_γ2 & own2)".
iPoseProof (term_name_agree with "own_γ1 own_γ2") as "<-".
by iApply (nown_valid_2 with "own1 own2").
Qed.

Lemma term_own_update t N (a a' : A) :
  a ~~> a' → term_own t N a ==∗ term_own t N a'.
Proof.
rewrite term_own_unseal.
iIntros (?) "(%γ' & #? & own)".
iMod (nown_update with "own") as "own"; eauto.
iModIntro. iExists γ'. eauto.
Qed.

#[global]
Instance term_own_core_persistent t N (a : A) :
  CoreId a → Persistent (term_own t N a).
Proof. rewrite term_own_unseal. apply _. Qed.

#[global]
Instance term_own_timeless t N (a : A) :
  Discrete a → Timeless (term_own t N a).
Proof. rewrite term_own_unseal. apply _. Qed.

#[global]
Instance term_own_ne t N : NonExpansive (@term_own A _ t N).
Proof. rewrite term_own_unseal. solve_proper. Qed.

#[global]
Instance term_own_proper t N : Proper ((≡) ==> (≡)) (@term_own A _ t N).
Proof. rewrite term_own_unseal. solve_proper. Qed.

Lemma term_own_op t N (a1 a2 : A) :
  term_own t N (a1 ⋅ a2) ⊣⊢ term_own t N a1 ∗ term_own t N a2.
Proof.
rewrite term_own_unseal.
iSplit.
- iIntros "(%γ' & #? & [own1 own2])".
  by iSplitL "own1"; iExists γ'; iSplit.
- iIntros "[(%γ1 & #own_γ1 & own1) (%γ2 & #own_γ2 & own2)]".
  iPoseProof (term_name_agree with "own_γ1 own_γ2") as "<-".
  iExists γ1. iSplit => //. by iSplitL "own1".
Qed.

#[global]
Instance from_sep_term_own t N (a b1 b2 : A) :
  IsOp a b1 b2 → FromSep (term_own t N a) (term_own t N b1) (term_own t N b2).
Proof.
by rewrite /IsOp /FromSep => ->; rewrite term_own_op.
Qed.

#[global]
Instance combine_sep_as_term_own t N (a b1 b2 : A) :
  IsOp a b1 b2 → CombineSepAs (term_own t N b1) (term_own t N b2) (term_own t N a).
Proof. exact: from_sep_term_own. Qed.

#[global]
Instance into_sep_term_own t N (a b1 b2 : A) :
  IsOp a b1 b2 → IntoSep (term_own t N a) (term_own t N b1) (term_own t N b2).
Proof.
by rewrite /IsOp /IntoSep => ->; rewrite term_own_op.
Qed.

Lemma term_own_mono t N (a1 a2 : A) : a1 ≼ a2 → term_own t N a2 -∗ term_own t N a1.
Proof.
case => ? ->.
rewrite term_own_op.
by iIntros "[??]".
Qed.

Lemma term_own_update_2 t N (a1 a2 a' : A) :
  a1 ⋅ a2 ~~> a' →
  term_own t N a1 -∗
  term_own t N a2 ==∗
  term_own t N a'.
Proof.
iIntros "% H1 H2".
iMod (term_own_update with "[H1 H2]") as "H" => //.
by iSplitL "H1".
Qed.

End TermOwn.

#[global] Typeclasses Opaque term_own.

Lemma term_token_alloc_aux (T : gset term) (P Q : iProp) E :
  (∀ t, ⌜t ∈ T⌝ -∗ P -∗ minted t -∗ False) -∗
  (∀ t, ⌜t ∈ T⌝ -∗ Q -∗ minted t) -∗
  (P ∧ |={E}=> Q) -∗
  term_meta_inv ={E}=∗
  term_meta_inv ∗ Q ∗ [∗ set] t ∈ T, term_token t ⊤.
Proof.
assert (∀ names : gmap term gname,
  dom names ## T →
  own term_meta_name (● ((to_agree <$> names) : gmap term _)) ==∗
  ∃ names' : gmap term gname,
  ⌜dom names' = dom names ∪ T⌝ ∗
  own term_meta_name (● ((to_agree <$> names') : gmap term _)) ∗
  [∗ set] t ∈ T, term_token t ⊤) as names_alloc.
{ induction T as [|t T fresh IH] using set_ind_L.
  - iIntros "%names _ own !>". iExists names.
    by rewrite right_id_L big_sepS_empty; iFrame.
  - iIntros "%names %dis own".
    have t_names : t ∉ dom names by set_solver.
    have {}dis : dom names ## T by set_solver.
    iMod gmeta_token_alloc as "(%γ & token)".
    iMod (own_update with "own") as "[own frag]".
    { eapply auth_update_alloc.
      apply (alloc_singleton_local_update _ t (to_agree γ)) => //.
      by rewrite lookup_fmap (_ : names !! t = None) // -not_elem_of_dom. }
    rewrite -fmap_insert.
    have {}dis: dom (<[t := γ]>names) ## T.
      rewrite dom_insert; set_solver.
    iMod (IH _ dis with "own") as "(%names' & %dom_names' & own & tokens)".
    iModIntro. iExists names'. iFrame.
    rewrite dom_names' dom_insert_L. iSplit; first by iPureIntro; set_solver.
    rewrite big_sepS_union; last by set_solver.
    iFrame. rewrite big_sepS_singleton.
    rewrite term_token_unseal. iExists γ. iFrame. }
iIntros "PE QE PQ (%names & own & #minted_names)".
iAssert (⌜dom names ## T⌝)%I as "%dis".
{ rewrite elem_of_disjoint. iIntros "%t %t_names %t_T".
  rewrite big_sepS_delete //. iDestruct "minted_names" as "[minted_t _]".
  iDestruct "PQ" as "[P _]".
  iApply ("PE" with "[//] P minted_t"). }
iMod (names_alloc _ dis with "own") as "(%names' & %dom_names & own & tokens)".
iDestruct "PQ" as "[_ >Q]".
iAssert ([∗ set] t ∈ T, minted t)%I as "#minted_T".
{ rewrite (big_sepS_forall _ T). iIntros "%t %t_T".
  by iApply ("QE" with "[//] Q"). }
iModIntro. iFrame. rewrite dom_names big_sepS_union //. by iSplit.
Qed.

Context `{!HasTermMetaCtx ctx}.

Lemma term_token_alloc (T : gset term) (P Q : iProp) E :
  ↑nroot.@"cryptis".@"meta" ⊆ E →
  ctx -∗
  (∀ t, ⌜t ∈ T⌝ -∗ P -∗ minted t -∗ False) -∗
  (∀ t, ⌜t ∈ T⌝ -∗ Q -∗ minted t) -∗
  (P ∧ |={E ∖ ↑nroot.@"cryptis".@"meta"}=> Q) ={E}=∗
  Q ∗ [∗ set] t ∈ T, term_token t ⊤.
Proof.
iIntros "%sub ctx H1 H2 H3".
iPoseProof (has_term_meta_ctx with "ctx") as "{ctx} #ctx".
iInv "ctx" as ">inv" => //.
iMod (term_token_alloc_aux with "H1 H2 H3 inv") as "(inv & post & token)".
iModIntro. by iFrame.
Qed.

End TermMeta.

Arguments term_token {Σ _} t E.
Arguments term_meta {Σ _ L _ _} t N x.
Arguments term_meta_set {Σ _ _ _ _} N x E t.
Arguments term_token_difference {Σ _} t E1 E2.
Arguments term_name {Σ _} t γ.
Arguments term_own {Σ _ A _} t N x.
Arguments term_own_alloc {Σ _ A _ t} N {_} a.
Arguments term_own_update {Σ _ A _ t N a} a'.
