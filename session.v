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
From iris.base_logic.lib Require Import auth.
From iris.heap_lang Require Import notation proofmode.
From crypto Require Import lib guarded term crypto primitives tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Session.

Context `{!cryptoG Σ, !heapG Σ}.
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

Inductive session_view := SessionView {
  s_role : role;
  s_init_id : term;
  s_resp_id : term;
  s_init_data : term;
  s_resp_data : term;
}.

Canonical session_viewO := leibnizO session_view.

Global Instance session_view_inhabited : Inhabited session_view :=
  populate (SessionView inhabitant inhabitant inhabitant
                        inhabitant inhabitant).

Definition session_statusR :=
  prodR (authR (optionUR unitR)) (agreeR session_viewO).

Definition session_mapUR := gmapUR term session_statusR.

Implicit Types t : term.
Implicit Types SM : gmap term (option unit * session_view).
Implicit Types s : session_view.

Definition s_key s :=
  if s.(s_role) is Init then s.(s_init_data) else s.(s_resp_data).

Definition session_status_auth p :=
  (● p.1, to_agree p.2) : session_statusR.
Definition session_status_frag p :=
  (◯ p.1, to_agree p.2) : session_statusR.
Definition session_status_both p :=
  session_status_auth p ⋅ session_status_frag p.

Definition swap_view s :=
  SessionView (swap_role s.(s_role))
              s.(s_init_id)
              s.(s_resp_id)
              s.(s_init_data)
              s.(s_resp_data).

Lemma swap_viewK s : swap_view (swap_view s) = s.
Proof. by case: s => [] []. Qed.

Definition to_session_map SM := session_status_both <$> SM.

Class sessionG := {
  session_inG  :> inG Σ (authR session_mapUR);
}.

Context `{!sessionG} (γ : gname) (N : namespace).
Context (sinv : role → term → term → term → term → iProp).

Definition sinv_int s :=
  let 'SessionView rl kA kB tA tB := s in
  sinv rl kA kB tA tB.

Global Instance sessionG_authG : authG _ _ :=
  AuthG Σ session_mapUR session_inG _.

Lemma session_status_auth_valid p : ✓ session_status_auth p.
Proof.
apply/pair_valid; split=> //.
apply/auth_auth_valid.
by case: p.1 => //.
Qed.

Lemma session_status_frag_valid p : ✓ session_status_frag p.
Proof.
apply/pair_valid; split=> //.
by case: p.1 => //.
Qed.

Definition session_auth p : iProp :=
  auth_own γ {[s_key p.2 := session_status_auth p]}.

Definition session_frag p : iProp :=
  auth_own γ {[s_key p.2 := session_status_frag p]}.

Global Instance session_frag_persistent p :
  Persistent (session_frag p).
Proof. apply _. Qed.

Lemma session_auth_frag_agree o1 s1 o2 s2 :
  s_key s1 = s_key s2 →
  session_auth (o1, s1) -∗
  session_frag (o2, s2) -∗
  ⌜o2 ≼ o1 ∧ s1 = s2⌝.
Proof.
rewrite /session_auth /session_frag => <- /=.
iIntros "own1 own2".
iPoseProof (own_valid_2 with "own1 own2") as "%s_valid"; iPureIntro.
move: s_valid; rewrite -auth_frag_op auth_frag_valid singleton_op.
rewrite -pair_op singleton_valid pair_valid.
by case=> [] /= /auth_both_valid [? _] /agree_op_invL' ?; eauto.
Qed.

Lemma session_frag_agree o1 s1 o2 s2 :
  s_key s1 = s_key s2 →
  session_frag (o1, s1) -∗
  session_frag (o2, s2) -∗
  ⌜s1 = s2⌝.
Proof.
rewrite /session_frag => <- /=.
iIntros "Hown1 Hown2".
iPoseProof (own_valid_2 with "Hown1 Hown2") as "%s_valid"; iPureIntro.
move: s_valid; rewrite -auth_frag_op auth_frag_valid singleton_op.
rewrite -pair_op singleton_valid pair_valid; case=> [] _.
exact/agree_op_invL'.
Qed.

Definition session_map_inv SM : iProp :=
  ([∗ map] t ↦ p ∈ SM,
     ⌜t = s_key p.2⌝ ∗
     crypto_meta t N () ∗
     (sinv_int p.2 ∨ session_frag (Some (), swap_view p.2)))%I.

Lemma session_map_inv_unregistered SM t :
  crypto_meta_token t (↑N) -∗
  session_map_inv SM -∗
  ⌜SM !! t = None⌝.
Proof.
iIntros "token inv".
destruct (SM !! t) as [[ac s]|] eqn:SM_t=> //.
rewrite /session_map_inv big_sepM_delete // /=.
iDestruct "inv" as "[(_ & meta & _) _]".
by iDestruct (crypto_meta_meta_token with "token meta") as "[]".
Qed.

Definition session_inv : iProp :=
  auth_inv γ to_session_map session_map_inv.

Definition session_ctx : iProp :=
  auth_ctx γ N to_session_map session_map_inv.

Lemma session_status_auth_included p1 p2 :
  session_status_auth p1 ≼ session_status_both p2 →
  p1 = p2.
Proof.
case: p1 p2 => [ac1 s1] [ac2 s2].
rewrite pair_included auth_included /= right_id agree_idemp.
case=> [] [] /Some_pair_included_total_2 [] _.
rewrite to_agree_included => e _; rewrite (leibniz_equiv _ _ e) {e}.
by rewrite to_agree_included => e; rewrite (leibniz_equiv _ _ e).
Qed.

Lemma session_auth_session_frag E p :
  ↑N ⊆ E →
  session_ctx -∗
  session_auth p ={E}=∗
  session_auth p ∗ session_frag p.
Proof.
iIntros (?) "#ctx auth".
iMod (auth_acc to_session_map session_map_inv
        with "[ctx auth]") as (SM) "(%lb & inv & close)" => //; eauto.
iMod ("close" $! SM {[s_key p.2 := session_status_both p]} with "[inv]")
    as "own"; last first.
  by rewrite -singleton_op auth_own_op.
iFrame; iPureIntro.
case/singleton_included_l: lb => [x []].
rewrite lookup_fmap option_equivE.
case SM_t: (SM !! s_key p.2) => [p'|] //= <-.
rewrite Some_included_total => /session_status_auth_included ?; subst p'.
rewrite /session_status_both -singleton_op.
apply: core_id_local_update.
apply/singleton_included_l; exists (session_status_both p).
rewrite lookup_fmap SM_t /session_status_both -pair_op; split.
  by rewrite option_equivE /=; split => //.
apply: Some_included_2; rewrite pair_op; exact: cmra_included_r.
Qed.

Lemma session_begin_aux s E :
  ↑N ⊆ E →
  session_ctx -∗
  sinv_int s -∗
  crypto_meta_token (s_key s) (↑N) ={E}=∗
  session_auth (None, s) ∗ session_frag (None, s).
Proof.
iIntros (?) "#ctx s_inv token".
iMod (auth_empty γ) as "#init".
iMod (auth_acc to_session_map session_map_inv
         with "[ctx init]") as "inv"; try by eauto.
iDestruct "inv" as (SM) "(_ & inv & close)".
iAssert (▷ ⌜SM !! s_key s = None⌝)%I as "# > %s_fresh".
  iModIntro.
  by iApply (session_map_inv_unregistered with "[token] [inv]").
iMod (crypto_meta_set _ () with "token") as "#meta"; eauto.
rewrite -auth_own_op singleton_op.
iApply ("close" $! (<[s_key s := (None, s)]>SM)); iSplit.
  iPureIntro; rewrite /to_session_map fmap_insert.
  apply alloc_singleton_local_update.
    by rewrite lookup_fmap s_fresh.
  rewrite pair_valid /= auth_both_valid agree_idemp; repeat split; eauto.
iModIntro; rewrite /session_map_inv big_sepM_insert //=.
by iFrame; iSplit.
Qed.

Lemma session_status_both_eq p :
  session_status_both p ≡ (● p.1 ⋅ ◯ p.1, to_agree p.2).
Proof.
by rewrite /session_status_both -pair_op agree_idemp.
Qed.

Lemma session_end_aux s E :
  ↑N ⊆ E →
  session_ctx -∗
  session_auth (None, s) -∗
  session_frag (None, swap_view s) ={E}=∗
  ▷ sinv_int (swap_view s).
Proof.
iIntros (sub) "ctx sessA #sessB".
rewrite /session_frag /session_auth /= /session_ctx.
rewrite /auth_ctx /auth_inv.
iInv "ctx" as "inv"; iDestruct "inv" as (SM) "[>own inv]".
set f1 := {[s_key s := _]}.
set f2 := {[s_key (swap_view s) := _]}.
iAssert (▷ ⌜f1 ⋅ f2 ≼ to_session_map SM⌝)%I
    with "[sessA sessB own]" as "# > %SM_s".
  iCombine "sessA sessB" as "{sessB} sess".
  iModIntro; rewrite -auth_own_op.
  by iDestruct (own_valid_2 with "own sess") as % [? ?]%auth_both_valid.
pose proof (transitivity (cmra_included_l _ _) SM_s) as SM_sA.
pose proof (transitivity (cmra_included_r _ _) SM_s) as SM_sB.
case/singleton_included_l: SM_sA => [] _ [] <- /=.
rewrite lookup_fmap; case SM_sA: (SM !! _) => [[oA s']|] //=; last first.
  by case=> [] [?|]; rewrite option_equivE.
rewrite Some_included_total pair_included agree_idemp /=.
rewrite auth_included /= right_id.
case=> [] [] /Some_pair_included_total_2 [] _ /to_agree_included e_oA _.
have {}e_oA: oA = None by exact: leibniz_equiv.
subst oA.
move=> /to_agree_included e.
have {}e : s = s' by exact: leibniz_equiv.
subst s'.
case/singleton_included_l: SM_sB => [] _ [] <- /=.
rewrite lookup_fmap; case SM_sB: (SM !! _) => [[oB s']|] //=; last first.
  by case=> [] [?|]; rewrite option_equivE.
rewrite Some_included_total pair_included agree_idemp /=.
case=> [] _ /to_agree_included e.
have {}e : swap_view s = s' by exact: leibniz_equiv.
subst s'.
have ne: s_key s ≠ s_key (swap_view s).
  move=> e; move: SM_sB; rewrite -e SM_sA; case => _ /(f_equal s_role) /=.
  by case: (s_role s).
rewrite {1}/session_map_inv (big_sepM_delete _ SM (s_key (swap_view s))) //.
iDestruct "inv" as "[(_ & #meta & inv_s) inv]".
iAssert (▷ (sinv_int (swap_view s) ∗ own γ (◯ f1)))%I
    with "[sessA inv_s]" as "(res & >sessA)".
  iModIntro.
  iDestruct "inv_s" as "[H|sessA']"; first by iSplitL "H".
  iDestruct (session_auth_frag_agree with "sessA sessA'") as % [contra _].
    by rewrite /= swap_viewK.
  by case: contra => [[?|]]; rewrite option_equivE.
rewrite /session_auth /auth_own.
iCombine "sessA sessB" as "{sessB} sess".
iCombine "own sess" as "own".
iMod (own_update with "own") as "[own sess]".
  apply: auth_update.
  apply: op_local_update_frame.
  apply: (insert_local_update _ _ (s_key s)).
  - by rewrite lookup_fmap SM_sA.
  - by rewrite lookup_singleton.
  rewrite /session_status_both /session_status_auth /session_status_frag /=.
  rewrite -pair_op agree_idemp.
  apply: prod_local_update_1.
  rewrite -[● None as X in (_, X)]right_id.
  apply: auth_local_update.
  - apply: (alloc_option_local_update ()) => //.
  - reflexivity.
  - by [].
iDestruct "sess" as "[sessA #sessB]".
rewrite insert_singleton -(session_status_both_eq (Some tt, s)).
rewrite -singleton_op; iDestruct "sessA" as "[_ #sessA]".
iModIntro; iSplitL "own inv".
  iModIntro.
  iExists (<[s_key s := (Some (), s)]>SM).
  rewrite /to_session_map fmap_insert session_status_both_eq /=.
  iFrame.
  rewrite /session_map_inv big_sepM_insert_delete.
  rewrite big_sepM_delete; last first.
    rewrite lookup_delete_ne; last eauto; eauto.
  iDestruct "inv" as "[inv_s inv]".
  iSplitL "inv_s"; first by iFrame.
  rewrite (big_sepM_delete _ (delete (s_key s) SM)); last first.
    rewrite lookup_delete_ne; last eauto; eauto.
  iSplitR "inv".
    rewrite /= swap_viewK; do ![iSplit => //]; by iRight.
  by rewrite delete_commute.
eauto.
Qed.

Definition session rl kA kB tA tB : iProp :=
  session_frag (None, SessionView rl kA kB tA tB).

Global Instance session_persistent rl kA kB tA tB :
  Persistent (session rl kA kB tA tB).
Proof. apply _. Qed.

Lemma session_agree rl kA1 kB1 tA1 tB1 kA2 kB2 tA2 tB2 :
  (if rl is Init then tA1 else tB1) =
  (if rl is Init then tA2 else tB2) →
  session rl kA1 kB1 tA1 tB1 -∗
  session rl kA2 kB2 tA2 tB2 -∗
  ⌜kA1 = kA2 ∧ kB1 = kB2 ∧ tA1 = tA2 ∧ tB1 = tB2⌝.
Proof.
iIntros (?) "s1 s2".
iDestruct (session_frag_agree with "s1 s2") as "%e" => //.
by case: e.
Qed.

Lemma session_begin E rl kA kB tA tB :
  ↑N ⊆ E →
  session_ctx -∗
  sinv rl kA kB tA tB -∗
  crypto_meta_token (if rl is Init then tA else tB) (↑N) ={E}=∗
  session rl kA kB tA tB ∗
  (session (swap_role rl) kA kB tA tB ={E}=∗ ▷ sinv (swap_role rl) kA kB tA tB).
Proof.
iIntros (?) "#ctx inv token".
iMod (@session_begin_aux (SessionView rl kA kB tA tB)
        with "ctx inv token") as "[auth frag]" => //.
iModIntro; iSplitR "auth" => //.
by iIntros "frag"; iApply (session_end_aux with "ctx auth frag").
Qed.

Lemma session_beginG `{Decision G} E rl kA kB tA tB :
  ↑N ⊆ E →
  session_ctx -∗
  guarded G (sinv rl kA kB tA tB) -∗
  guarded G (crypto_meta_token (if rl is Init then tA else tB) (↑N)) ={E}=∗
  guarded G (session rl kA kB tA tB) ∗
  (guarded G (session (swap_role rl) kA kB tA tB) ={E}=∗
   ▷ guarded G (sinv (swap_role rl) kA kB tA tB)).
Proof.
iIntros (?) "#ctx inv token".
rewrite /guarded; case: decide => //= _.
by iApply (session_begin with "ctx inv token").
Qed.

End Session.

Arguments sessionG : clear implicits.
Arguments session_begin {Σ _ _ _} {γ N sinv} E rl kA kB tA tB.
Arguments session_beginG {Σ _ _ _} {γ N sinv} G {_} E rl kA kB tA tB.
