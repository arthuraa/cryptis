(**

This file includes definitions and lemmas for reasoning about session
authentication.  To initiate a session, two agents [A] and [B] exchange terms
[tA] and [tB].  Typically, these terms are secrets and used to generate a new
key to encrypt the communication during the session.  We _define_ authentication
as the ability to exchange resources: if an honest agent [A] owns some resource
[P A B tA tB], and an honest [B] owns [Q A B tA tB], after authenticating the
session they swap ownership of these resources.  This is formalized by the
[session_begin] lemma below.  The lemma states that A can give up their
resources in exchange for two things:

1. A [session] "certificate", which represents A's intent to initiate a session
   with B.

2. The ability to obtain B's resources, provided that A can exhibit a [session]
   certificate for B.

The [session] certificate is persistent, and thus can be included in terms. To
verify an authentication protocol, A uses [session_begin] to declare a new
session.  It sends its certificate to B via an encrypted message or a digital
signature.  It then waits for a reply from B with a matching certificate to
obtain B's resource.  The file nsl.v contains an example of this idiom.

*)

From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl namespace_map frac.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Session.

Context `{!cryptisG Σ, !heapG Σ}.
Notation iProp  := (iProp Σ).
Notation iPropI := (iPropI Σ).

Inductive role := Init | Resp.

Canonical roleO := leibnizO role.

Implicit Types rl : role.

Global Instance role_inhabited : Inhabited role := populate Init.

Lemma role_equivI rl1 rl2 :
  rl1 ≡ rl2 ⊣⊢@{iPropI}
  match rl1, rl2 with
  | Init, Init | Resp, Resp => True
  | _, _ => False
  end.
Proof.
by case: rl1 rl2=> [] []; iSplit=> //.
Qed.

Definition bool_of_role rl :=
  if rl is Init then true else false.

Definition role_of_bool (b : bool) : role :=
  if b then Init else Resp.

Lemma bool_of_roleK : Cancel (=) role_of_bool bool_of_role.
Proof. by case. Qed.

Global Instance role_eq_dec : EqDecision role.
Proof.
refine (λ rl1 rl2,
          match rl1, rl2 with
          | Init, Init => left _
          | Resp, Resp => left _
          | _, _ => right _
          end); abstract intuition congruence.
Defined.

Global Instance role_countable : Countable role.
Proof. apply (inj_countable' _ _ bool_of_roleK). Qed.

Definition swap_role rl :=
  if rl is Init then Resp else Init.

Definition session_statusR := authR (optionUR unitR).

Definition session_mapUR := gmapUR term session_statusR.

Implicit Types t : term.
Implicit Types SM : gmap term (option unit).

Definition session_status_auth p := ● p : session_statusR.
Definition session_status_frag p := ◯ p : session_statusR.
Definition session_status_both p :=
  session_status_auth p ⋅ session_status_frag p.

Definition to_session_map SM := session_status_both <$> SM.

Definition sessionR := authR session_mapUR.

Class sessionG := {
  session_inG    :> inG Σ sessionR;
}.

Context `{TermMeta Σ term_meta term_meta_token, Countable X}.
Context `{!sessionG} (N : namespace).
Context (P : role → term → term → X → iProp).
Arguments term_meta {_ _ _} _ _ _.

Let sinv rl tA tB x :=
  P rl (if rl is Init then tA else tB)
       (if rl is Init then tB else tA) x.

Lemma session_status_auth_valid p : ✓ session_status_auth p.
Proof. by apply/auth_auth_valid; case: p. Qed.

Lemma session_status_frag_valid p : ✓ session_status_frag p.
Proof. apply/auth_frag_valid; by case: p. Qed.

Definition session_auth γ rl t (k : term) (x : X) o : iProp :=
  own γ (◯ {[t := session_status_auth o]}) ∧
  term_meta t N (x, rl, k).

Definition session_frag γ rl t (k : term) (x : X) o : iProp :=
  own γ (◯ {[t := session_status_frag o]}) ∧
  term_meta t N (x, rl, k).

Global Instance session_frag_persistent γ rl t k x o :
  Persistent (session_frag γ rl t k x o).
Proof. apply _. Qed.

Lemma session_auth_frag_agree γ t rl1 rl2 k1 k2 x1 x2 o1 o2 :
  session_auth γ rl1 t k1 x1 o1 -∗
  session_frag γ rl2 t k2 x2 o2 -∗
  ⌜rl1 = rl2 ∧ k1 = k2 ∧ x1 = x2 ∧ o2 ≼ o1⌝.
Proof.
iIntros "[own1 meta1] [own2 meta2]".
iPoseProof (term_meta_agree with "meta1 meta2") as "%e".
case: e => <- <- <-.
iPoseProof (own_valid_2 with "own1 own2") as "%s_valid"; iPureIntro.
do 3!split => //.
move: s_valid; rewrite -auth_frag_op auth_frag_valid singleton_op.
by rewrite singleton_valid => /auth_both_valid_discrete [? _]; eauto.
Qed.

Lemma session_frag_agree γ rl1 rl2 t k1 k2 x1 x2 o1 o2 :
  session_frag γ rl1 t k1 x1 o1 -∗
  session_frag γ rl2 t k2 x2 o2 -∗
  ⌜rl1 = rl2 ∧ k1 = k2 ∧ x1 = x2⌝.
Proof.
iIntros "[_ meta1] [_ meta2]".
iPoseProof (term_meta_agree with "meta1 meta2") as "%e"; iPureIntro.
repeat split; congruence.
Qed.

Definition session_map_inv γ SM : iProp :=
  ([∗ map] t ↦ o ∈ SM, ∃ k rl (x : X),
     term_meta t N (x, rl, k) ∧
     (sinv rl t k x ∨ session_frag γ (swap_role rl) k t x (Some ())))%I.

Lemma session_map_inv_unregistered γ SM t :
  term_meta_token t (↑N) -∗
  session_map_inv γ SM -∗
  ⌜SM !! t = None⌝.
Proof.
iIntros "fresh inv".
destruct (SM !! t) as [o|] eqn:SM_t=> //.
rewrite /session_map_inv big_sepM_delete // /=.
iDestruct "inv" as "[inv _]".
iDestruct "inv" as (k rl x) "(not_fresh & _)".
by iDestruct (term_meta_meta_token with "fresh not_fresh") as "[]".
Qed.

Definition session_ctx γ : iProp :=
  inv N (∃ SM, own γ (● to_session_map SM) ∗ session_map_inv γ SM).

Lemma session_ctx_acc E γ a :
  ↑N ⊆ E →
  session_ctx γ ∗ own γ (◯ a) ={E,E ∖ ↑N}=∗ ∃ SM,
    ⌜a ≼ to_session_map SM⌝ ∗ ▷ session_map_inv γ SM ∗ ∀ SM' b,
    ⌜(to_session_map SM, a) ~l~> (to_session_map SM', b)⌝ ∗
    ▷ session_map_inv γ SM' ={E∖↑N,E}=∗
    own γ (◯ b).
Proof.
iIntros "%sub [ctx own_f]".
iMod (inv_acc with "ctx") as "[ctx close]" => //.
iDestruct "ctx" as (SM) "[>own_a inv]".
iPoseProof (own_valid_2 with "own_a own_f") as "%valid".
move: valid; rewrite auth_both_valid_discrete; case=> a_incl _.
iModIntro; iExists SM; iFrame; iSplit => //.
iIntros (SM' b) "[%upd inv]".
iCombine "own_a own_f" as "own".
iMod (own_update with "own") as "own".
  by apply: auth_update; eauto.
iDestruct "own" as "[own_a own_f]".
iMod ("close" with "[own_a inv]") as "_"; eauto.
by iModIntro; iExists SM'; iFrame.
Qed.

Lemma session_alloc E : ⊢ |={E}=> ∃ γ, session_ctx γ.
Proof.
iStartProof.
iMod (own_alloc (● (to_session_map ∅))) as (γ) "own".
  by rewrite auth_auth_valid.
iExists γ; iApply inv_alloc.
iModIntro; iExists ∅; iFrame.
by rewrite /session_map_inv big_sepM_empty.
Qed.

Lemma session_status_auth_included p1 p2 :
  session_status_auth p1 ≼ session_status_both p2 →
  p1 = p2.
Proof.
rewrite auth_auth_included; exact: leibniz_equiv.
Qed.

Lemma session_auth_session_frag E γ rl t k x o :
  ↑N ⊆ E →
  session_ctx γ -∗
  session_auth γ rl t k x o ={E}=∗
  session_auth γ rl t k x o ∗ session_frag γ rl t k x o.
Proof.
iIntros (?) "#ctx [auth #meta]".
iMod (session_ctx_acc with "[ctx auth]") as (SM) "(%lb & inv & close)" => //; eauto.
iMod ("close" $! SM {[t := session_status_both o]} with "[inv]")
    as "own"; last first.
  rewrite -singleton_op auth_frag_op own_op /session_auth /session_frag.
  by iDestruct "own" as "[own1 own2]"; iFrame; eauto.
iFrame; iPureIntro.
case/singleton_included_l: lb => [p []].
rewrite lookup_fmap option_equivE.
case SM_t: (SM !! t) => [p'|] //= <-.
rewrite Some_included_total => /session_status_auth_included ?; subst p'.
rewrite /session_status_both -singleton_op.
apply: core_id_local_update.
apply/singleton_included_l; exists (session_status_both o).
rewrite lookup_fmap SM_t /session_status_both; split.
  by rewrite option_equivE /=; split => //.
apply: Some_included_2; exact: cmra_included_r.
Qed.

Lemma session_begin_aux γ rl t k x E :
  ↑N ⊆ E →
  session_ctx γ -∗
  sinv rl t k x -∗
  term_meta_token t (↑N) ={E}=∗
  session_auth γ rl t k x None ∗ session_frag γ rl t k x None.
Proof.
iIntros (?) "#ctx s_inv fresh".
iAssert (|==> own γ (◯ ε))%I as ">#init".
  by iApply own_unit.
iMod (session_ctx_acc with "[ctx init]") as "inv"; try by eauto.
iDestruct "inv" as (SM) "(_ & inv & close)".
iAssert (▷ ⌜SM !! t = None⌝)%I as "# > %s_fresh".
  iModIntro.
  by iApply (session_map_inv_unregistered with "[fresh] [inv]").
iMod (term_meta_set _ _ (x, rl, k) with "fresh") as "#not_fresh"; eauto.
iMod ("close" $! (<[t := None]>SM) {[t := session_status_both None]}
        with "[s_inv inv]") as "own"; first iSplit.
- iPureIntro; rewrite /to_session_map fmap_insert.
  apply alloc_singleton_local_update.
    by rewrite lookup_fmap s_fresh.
  by rewrite auth_both_valid; repeat split; eauto.
- iModIntro; rewrite /session_map_inv big_sepM_insert //=.
  by iFrame; iExists _, _; eauto.
rewrite -singleton_op auth_frag_op.
iDestruct "own" as "[own1 own2]".
by rewrite /session_auth /session_frag; iFrame; eauto.
Qed.

Lemma session_end_aux γ rl t s x E :
  ↑N ⊆ E →
  session_ctx γ -∗
  session_auth γ rl t s x None -∗
  session_frag γ (swap_role rl) s t x None ={E}=∗
  ▷ sinv (swap_role rl) s t x.
Proof.
iIntros (sub) "ctx [sessA #metaA] [#sessB #metaB]".
rewrite /session_frag /session_auth /= /session_ctx.
iInv "ctx" as "inv"; iDestruct "inv" as (SM) "[>own inv]".
set f1 := {[t := _]}.
set f2 := {[s := _]}.
iAssert (▷ ⌜f1 ⋅ f2 ≼ to_session_map SM⌝)%I
    with "[sessA sessB own]" as "# > %SM_s".
  iCombine "sessA sessB" as "{sessB} sess".
  iModIntro.
  by iDestruct (own_valid_2 with "own sess") as % [? ?]%auth_both_valid_discrete.
pose proof (transitivity (cmra_included_l _ _) SM_s) as SM_sA.
pose proof (transitivity (cmra_included_r _ _) SM_s) as SM_sB.
case/singleton_included_l: SM_sA => [] _ [] <- /=.
rewrite lookup_fmap; case SM_sA: (SM !! _) => [oA|] //=; last first.
  by case=> [] [?|]; rewrite option_equivE.
rewrite Some_included_total /= => /session_status_auth_included ?.
subst oA.
case/singleton_included_l: SM_sB => [] _ [] <- /=.
rewrite lookup_fmap; case SM_sB: (SM !! _) => [oB|] //=; last first.
  by case=> [] [?|]; rewrite option_equivE.
rewrite Some_included_total /= => _.
rewrite {1}/session_map_inv (big_sepM_delete _ SM s) //.
iDestruct "inv" as "[inv_s inv]".
have ? : Inhabited X by exact: populate x.
iDestruct "inv_s" as (k rl' x') "[#not_fresh inv_s]".
iAssert (▷ (sinv (swap_role rl) s t x ∗ own γ (◯ f1)))%I
    with "[sessA inv_s]" as "(res & >sessA)".
  iModIntro.
  iPoseProof (term_meta_agree with "metaB not_fresh") as "%e".
  case: e => <- <- <-.
  iDestruct "inv_s" as "[H|sessA']"; first by iSplitL "H".
  iAssert (session_auth γ rl t s x None) with "[sessA]" as "sessA".
    by iSplit.
  iDestruct (session_auth_frag_agree with "sessA sessA'") as % (_ & _ & _ & contra).
  by case: contra => [[?|]]; rewrite option_equivE.
rewrite /session_auth.
iCombine "own sessA sessB" as "{sessB} own".
iMod (own_update with "own") as "[own sess]".
  apply: auth_update.
  apply: op_local_update_frame.
  apply: (insert_local_update _ _ t).
  - by rewrite lookup_fmap SM_sA.
  - by rewrite lookup_singleton.
  rewrite /session_status_both /session_status_auth /session_status_frag /=.
  rewrite -[● None as X in (_, X)]right_id.
  apply: auth_local_update.
  - apply: (alloc_option_local_update ()) => //.
  - reflexivity.
  - by [].
iDestruct "sess" as "[sessA #sessB]".
rewrite insert_singleton -singleton_op.
iDestruct "sessA" as "[_ #sessA]".
iFrame; iModIntro; iSplitL; eauto; iModIntro.
iClear "not_fresh".
iExists (<[t := Some ()]>SM).
rewrite /to_session_map fmap_insert /=; iFrame.
case: (decide (t = s)) => [?|ne]; first subst s.
  rewrite /session_map_inv big_sepM_insert_delete; iFrame.
  by iExists t, rl, x; iSplit => //; iRight; iSplit.
rewrite /session_map_inv big_sepM_insert_delete.
rewrite big_sepM_delete; last first.
  rewrite lookup_delete_ne; last eauto; eauto.
iDestruct "inv" as "[inv_s inv]".
iSplitL "inv_s"; first by iFrame.
rewrite (big_sepM_delete _ (delete t SM)); last first.
  rewrite lookup_delete_ne; last eauto; eauto.
iFrame; iSplitR "inv"; last by rewrite delete_commute.
iExists _, _, _; iSplit => //.
by iRight; case: (rl); iSplit.
Qed.

Definition session γ rl tI tR x : iProp :=
  session_frag γ rl
               (if rl is Init then tI else tR)
               (if rl is Init then tR else tI) x None.

Global Instance session_persistent γ rl tI tR x :
  Persistent (session γ rl tI tR x).
Proof. apply _. Qed.

Global Instance session_timeless γ rl tI tR x :
  Timeless (session γ rl tI tR x).
Proof. apply _. Qed.

Lemma session_agree γ rl tI1 tI2 tR1 tR2 x1 x2 :
  (if rl is Init then tI1 = tI2 else tR1 = tR2) →
  session γ rl tI1 tR1 x1 -∗
  session γ rl tI2 tR2 x2 -∗
  ⌜(if rl is Init then tR1 = tR2 else tI1 = tI2) ∧ x1 = x2⌝.
Proof.
case: rl => ->.
all: iIntros "s1 s2".
all: by iDestruct (session_frag_agree with "s1 s2") as "(% & % & %)".
Qed.

Lemma session_begin E γ rl tI tR x :
  ↑N ⊆ E →
  session_ctx γ -∗
  P rl tI tR x -∗
  term_meta_token (if rl is Init then tI else tR) (↑N) ={E}=∗
  session γ rl tI tR x ∗
  (session γ (swap_role rl) tI tR x ={E}=∗ ▷ P (swap_role rl) tI tR x).
Proof.
rewrite /=; iIntros (?) "#ctx inv token".
iMod (@session_begin_aux γ rl (if rl is Init then tI else tR)
        (if rl is Init then tR else tI)
        with "ctx [inv] token") as "[auth frag]" => //.
  by rewrite /sinv; case: rl; eauto.
iModIntro; iSplitR "auth" => //.
rewrite /session; case: rl => /=.
all: by iIntros "frag"; iApply (session_end_aux with "ctx auth frag").
Qed.

End Session.

Definition sessionΣ : gFunctor :=
  GFunctor sessionR.

Arguments sessionG Σ : clear implicits.
Arguments session_alloc {Σ _} term_meta {X _ _ _} N P.
Arguments session_begin {Σ _ _ _ _ _ _ _ _}  {N P} E γ rl tI tR.
Arguments session_ctx {Σ _} term_meta {_ _ _ _} N P γ.
Arguments session {Σ} term_meta {_ _ _ _} N γ _ _ _.

Instance subG_sessionΣ {Σ} : subG sessionΣ Σ → sessionG Σ.
Proof. solve_inG. Qed.
