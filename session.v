(**

This file defines infrastructure for reasoning about correspondence properties,
which are common correctness criteria for authentication protocols.  A protocol
satisfies correspondence if the protocol participants agree on which data items
were exchanged in the protocol (assuming that the participants are honest).  The
data items are often fresh secrets used to establish a shared session key
between the participants.

We formalize correspondence by means of a predicate [correspondence kI kR tI
tR], which says that the participants identified by [kI] and [kR] agree that the
data items [tI] and [tR] correspond to the same session.  This predicate
satisfies two important properties:

1. it is persistent (cf. [correspondence_persistent]);

2. it guarantees that the data items completely determine each other (cf.
   [correspondence_agreeL] and [correspondence_agreeR]);

3. each data item was chosen by exactly one role (cf. [correspondence_agreeLR]).

Taken together, these properties imply that, once we know that two terms are
connected to some session, they will never be connected to other sessions of the
same protocol.

Suppose that Alice wants to communicate with Bob.  To prove correspondence for a
protocol, we follow these steps:

1. Alice uses [session_alloc_init] to associate some data item [tA] with a fresh
session with Bob.  To ensure that [tA] has not been used for other sessions,
Alice must prove that it has ownership of [crypto_meta_token tA (↑N)], where [N]
is some fixed namespace associated with the protocol.  Alice obtains two
predicates [session_auth] and [session_frag], which describe the state of the
new session.  (The predicates are guarded by a secrecy level because if we try
to communicate with a dishonest party, there is nothing we can guarantee.)  The
[None] argument signals that Alice has not attached any data items to this
session belonging to Bob.

2. When Bob receives a data item [tA], it generates another data item [tB] and
binds [tB] to [tA] (cf. [session_alloc_resp]).  The result of this lemma is
similar to Alice's, except that [session_frag] and [session_auth] record that
Bob does have a putative data item from Alice.

3. Alice combines her [session_auth] knowledge with a matching [session_frag]
from Bob (cf. [session_update]).  This causes [tA] to be irreversibly tied to
[tB].

4. Each agent combines their matching fragments to conclude [correspondence].

The agents may communicate their fragments to each other via encrypted messages
or signatures.  The implementation of the NSL protocol in [nsl.v] illustrates
this pattern for encryption.

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
Context (sinv : session_view → iProp).

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

Definition correspondence kI kR tI tR : iProp :=
  session_frag (None, SessionView Init kI kR tI tR) ∗
  session_frag (None, SessionView Resp kI kR tI tR).

Global Instance correspondence_persistent kI kR tI tR :
  Persistent (correspondence kI kR tI tR).
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

Lemma correspondence_agreeL kI1 kI2 kR1 kR2 tI tR1 tR2 :
  correspondence kI1 kR1 tI tR1 -∗
  correspondence kI2 kR2 tI tR2 -∗
  ⌜kI1 = kI2 ∧ kR1 = kR2 ∧ tR1 = tR2⌝.
Proof.
iIntros "[H1 _] [H2 _]".
iPoseProof (session_frag_agree with "H1 H2") as "/= %e" => //.
by iPureIntro; repeat split; congruence.
Qed.

Lemma correspondence_agreeR kI1 kI2 kR1 kR2 tI1 tI2 tR :
  correspondence kI1 kR1 tI1 tR -∗
  correspondence kI2 kR2 tI2 tR -∗
  ⌜kI1 = kI2 ∧ kR1 = kR2 ∧ tI1 = tI2⌝.
Proof.
iIntros "[_ H1] [_ H2]".
iPoseProof (session_frag_agree with "H1 H2") as "/= %e" => //.
by iPureIntro; repeat split; congruence.
Qed.

Lemma correspondence_agreeLR kI1 kI2 kR1 kR2 t tI tR :
  correspondence kI1 kR1 t tR -∗
  correspondence kI2 kR2 tI t -∗
  False.
Proof.
iIntros "[H1 _] [_ H2]".
by iPoseProof (session_frag_agree with "H1 H2") as "/= %e".
Qed.

Definition session_map_inv SM : iProp :=
  ([∗ map] t ↦ p ∈ SM,
     ⌜t = s_key p.2⌝ ∗
     crypto_meta t N () ∗
     (sinv p.2 ∨ session_frag (Some (), swap_view p.2)))%I.

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

Lemma session_begin s E :
  ↑N ⊆ E →
  session_ctx -∗
  sinv s -∗
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

(*
Lemma session_map_auth_included p SM :
  session_status_auth
{[t := session_status_auth s]} ≼ to_session_map SM ↔
  SM !! t = Some s.
Proof.
split.
- move=> e; apply/leibniz_equiv.
  case/singleton_included_l: e=> x [].
  rewrite lookup_fmap option_equivE.
  case: (SM !! t)=> [s'|] //= <-.
  rewrite Some_included; case.
  + by case=> /= _; rewrite option_equivE.
  + by rewrite session_status_auth_included=> <-.
- move=> e; apply/singleton_included_l.
  exists (session_status_both s).
  by rewrite lookup_fmap e /= Some_included session_status_auth_included; eauto.
Qed.

Lemma session_map_frag_included t s SM :
  {[t := session_view_frag s]} ≼ to_session_map SM ↔
  ∃ s', SM !! t = Some s' ∧ to_session_view' s ≼ to_session_view' s'.
Proof.
split.
- case/singleton_included_l=> x [].
  rewrite lookup_fmap option_equivE.
  case: (SM !! t)=> [s'|] //= <-.
  rewrite Some_included; case.
  + by case=> /=; rewrite option_equivE.
  + rewrite session_view_frag_included; eauto.
- case=> s' [H1 H2].
  apply/singleton_included_l.
  rewrite lookup_fmap H1 /=.
  exists (session_status_both s'); split=> //.
  by rewrite Some_included session_view_frag_included; right.
Qed.

Lemma session_frag_inv E t s :
  ↑N ⊆ E →
  session_ctx -∗
  session_frag t s ={E}=∗
  ▷ □ sinv (srole s) (sowner s) (sother s) t ∗
  ▷ (⌜is_Some (sdata s)⌝ → coherent_views t s).
Proof.
move=> sub; iIntros "#Hctx Hterm".
iMod (auth_acc to_session_map _ _ _ _ {[t := session_view_frag s]}
         with "[Hctx Hterm]") as "Hinv"; try by eauto.
iDestruct "Hinv" as (SM) "(%Hincl & #Hinv & Hclose)".
iMod ("Hclose" $! SM {[t := session_view_frag s]} with "[Hinv]").
  by eauto.
case/session_map_frag_included: Hincl=> s' [SM_t ss'].
iModIntro.
rewrite /sowner /sother /coherent_views.
case/to_session_view'_included: ss'=> -> [-> [-> e]].
iDestruct ("Hinv" $! _ _ SM_t) as "(?&?&?)".
iSplit => //; rewrite /coherent_views; iModIntro.
iDestruct 1 as (t') "%e'".
by move: e; rewrite e' => <-.
Qed.

Lemma session_frag_invG `{Decision G} E t s :
  ↑N ⊆ E →
  session_ctx -∗
  guarded G (session_frag t s) ={E}=∗
  ▷ guarded G (□ sinv (srole s) (sowner s) (sother s) t) ∗
  ▷ (⌜is_Some (sdata s)⌝ → guarded G (coherent_views t s)).
Proof.
iIntros (?) "#ctx #frag"; rewrite /guarded.
case: decide => // _.
by iApply session_frag_inv.
Qed.
*)

Lemma session_status_both_eq p :
  session_status_both p ≡ (● p.1 ⋅ ◯ p.1, to_agree p.2).
Proof.
by rewrite /session_status_both -pair_op agree_idemp.
Qed.

Lemma session_end E s :
  ↑N ⊆ E →
  session_ctx -∗
  session_auth (None, s) -∗
  session_frag (None, swap_view s) ={E}=∗
  ▷ sinv (swap_view s).
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
iAssert (▷ (sinv (swap_view s) ∗ own γ (◯ f1)))%I
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

End Session.

Arguments sessionG : clear implicits.
