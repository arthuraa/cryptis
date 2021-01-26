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

Inductive session_data := SessionData {
  srole : role;
  sinit : term;
  sresp : term;
  sdata : option term;
}.

Canonical session_dataO := leibnizO session_data.

Global Instance session_data_inhabited : Inhabited session_data :=
  populate (SessionData inhabitant inhabitant inhabitant inhabitant).

Definition sroleo s := swap_role s.(srole).

Definition sowner s :=
  if s.(srole) is Init then s.(sinit) else s.(sresp).

Definition sother s :=
  if s.(srole) is Init then s.(sresp) else s.(sinit).

Definition session_data' : Type :=
  agree role * agree term * agree term * agree (option term).

Definition session_data'R : cmraT :=
  prodR (prodR (prodR (agreeR roleO) (agreeR termO)) (agreeR termO))
        (optionR (agreeR termO)).

Implicit Types t : term.
Implicit Types SM : gmap term session_data.
Implicit Types s : session_data.

Definition session_mapUR :=
  gmapUR term (authR (optionUR session_data'R)).

Class sessionG := {
  session_inG  :> inG Σ (authR session_mapUR);
}.

Context `{!sessionG} (γ : gname) (N : namespace).
Context (sinv : role → term → term → term → iProp).

Global Instance sessionG_authG : authG _ _ :=
  AuthG Σ session_mapUR session_inG _.

Definition to_session_data' s : session_data'R :=
  (to_agree s.(srole), to_agree s.(sinit),
   to_agree s.(sresp), to_agree <$> s.(sdata)).

Global Instance to_session_data'_inj : Inj (=) (≡) to_session_data'.
Proof.
case=> [??? ot1] [??? ot2]; do 3![case]=> /=.
do 3![move=> /to_agree_inj ->].
case: ot2=> [t2|] /=; last first.
  by move=> /equiv_None; case: ot1.
case/fmap_Some_equiv=> t1 [-> /to_agree_inj e].
by apply leibniz_equiv in e; congruence.
Qed.

Lemma to_session_data'_valid s : ✓ to_session_data' s.
Proof.
rewrite /to_session_data'; repeat split=> //=.
by case: (sdata s).
Qed.

Lemma to_session_data'_validN n s : ✓{n} to_session_data' s.
Proof.
rewrite /to_session_data'; repeat split=> //=.
by case: (sdata s).
Qed.

Lemma to_session_data'_included s1 s2 :
  to_session_data' s1 ≼ to_session_data' s2 ↔
  s1.(srole) = s2.(srole) ∧
  s1.(sinit) = s2.(sinit) ∧
  s1.(sresp) = s2.(sresp) ∧
  match s1.(sdata) with
  | Some _ => s1.(sdata) = s2.(sdata)
  | _ => True
  end.
Proof.
rewrite !pair_included; split.
- do 3![case]=> /=.
  rewrite !to_agree_included => -> -> -> edata.
  repeat split; case: (sdata s1) edata=> [t1|] //=.
  rewrite option_included; case=> //.
  destruct 1 as (t1' & s2' & e1 & e2 & e3).
  case: (sdata s2) e1 e2 e3=> [t2|] //= [<-] [<-].
  by rewrite to_agree_included; case=> [/to_agree_inj ->|->].
- do 3![case=> ->]; move=> edata; intuition.
  rewrite option_included.
  case: (sdata s1) edata=> [t1|] /=; last by left.
  by move=> <-; right; exists (to_agree t1), (to_agree t1); eauto.
Qed.

Lemma to_session_data'_included_eq s1 s2 :
  to_session_data' s1 ≼ to_session_data' s2 →
  is_Some s1.(sdata) →
  s1 = s2.
Proof.
move=> eincl [t e].
case: s1 s2 e eincl => [????] [????] /= ->.
rewrite to_session_data'_included /=.
by case=> <- [<- [<- <-]].
Qed.

Definition session_data_auth s := ● (Some (to_session_data' s)).
Definition session_data_frag s := ◯ (Some (to_session_data' s)).
Definition session_data_auth_frag s :=
  session_data_auth s ⋅ session_data_frag s.

Lemma session_data_auth_included s1 s2 :
  session_data_auth s1 ≼ session_data_auth_frag s2 ↔ s1 = s2.
Proof.
split; last by move=> ->; exists (session_data_frag s2).
rewrite auth_included /= Some_included.
destruct 1 as [[[_ e]|e] _].
- rewrite /= in e.
  apply to_agree_inj in e.
  apply Some_equiv_inj in e.
  by apply to_session_data'_inj in e.
- move: e; rewrite pair_included; case=> _.
  rewrite to_agree_included=> e.
  by apply Some_equiv_inj, to_session_data'_inj in e.
Qed.

Lemma session_data_frag_included s1 s2 :
  session_data_frag s1 ≼ session_data_auth_frag s2 ↔
  to_session_data' s1 ≼ to_session_data' s2.
Proof.
split.
- rewrite auth_included.
  case=> _ /=; rewrite ucmra_unit_left_id.
  by rewrite Some_included; case=> [->|].
- move=> e; transitivity (session_data_frag s2).
    by rewrite auth_included /= Some_included; eauto.
  by exists (session_data_auth s2); rewrite cmra_comm.
Qed.

Lemma session_data_auth_valid s : ✓ session_data_auth s.
Proof.
rewrite auth_valid_eq /=; split=> // n.
exists (Some (to_session_data' s)); split=> //.
split.
- by exists (Some (to_session_data' s)); rewrite ucmra_unit_left_id.
- apply Some_validN, to_session_data'_validN.
Qed.

Lemma session_data_frag_valid s : ✓ session_data_frag s.
Proof. by apply auth_frag_valid, to_session_data'_valid. Qed.

Lemma session_data_valid s1 s2 :
  ✓ (session_data_auth s1 ⋅ session_data_frag s2) ↔
  to_session_data' s2 ≼ to_session_data' s1.
Proof.
rewrite auth_both_valid Some_included; split.
- by case=> [[->|?] _].
- move=> e; intuition eauto.
  rewrite Some_valid; exact: to_session_data'_valid.
Qed.

Lemma session_data_auth_frag_valid s : ✓ session_data_auth_frag s.
Proof. exact/session_data_valid. Qed.

Definition to_session_map SM : gmap term _ :=
  session_data_auth_frag <$> SM.

Definition session_auth t s : iProp :=
  auth_own γ {[t := session_data_auth s]}.

Definition session_frag t s : iProp :=
  auth_own γ {[t := session_data_frag s]}.

Global Instance session_frag_persistent t s :
  Persistent (session_frag t s).
Proof. apply _. Qed.

Definition correspondence kI kR tI tR : iProp :=
  session_frag tI (SessionData Init kI kR (Some tR)) ∗
  session_frag tR (SessionData Resp kI kR (Some tI)).

Global Instance correspondence_persistent kI kR tI tR :
  Persistent (correspondence kI kR tI tR).
Proof. apply _. Qed.

Lemma session_auth_frag_agree t s1 s2 :
  session_auth t s1 -∗
  session_frag t s2 -∗
  ⌜to_session_data' s2 ≼ to_session_data' s1⌝.
Proof.
iIntros "Hown1 Hown2".
iPoseProof (own_valid_2 with "Hown1 Hown2") as "%Hvalid".
iPureIntro; apply/session_data_valid.
by rewrite auth_valid_discrete /= singleton_op singleton_valid in Hvalid *.
Qed.

Lemma session_frag_agree t s1 s2 :
  session_frag t s1 -∗
  session_frag t s2 -∗
  ⌜s1.(srole) = s2.(srole) ∧
   s1.(sinit) = s2.(sinit) ∧
   s1.(sresp) = s2.(sresp) ∧
   (is_Some s1.(sdata) → is_Some s2.(sdata) → s1.(sdata) = s2.(sdata))⌝.
Proof.
iIntros "Hown1 Hown2".
iPoseProof (own_valid_2 with "Hown1 Hown2") as "%Hvalid".
iPureIntro.
move: Hvalid; rewrite auth_valid_eq /= singleton_op singleton_valid.
rewrite /session_data_frag auth_valid_eq /= -Some_op Some_valid.
rewrite -!pair_op !pair_valid.
case=> [] [] [] /agree_op_invL' ? /agree_op_invL' ? /agree_op_invL' ? Hdata.
do ![split => //].
move=> H1 H2; case: H1 H2 Hdata => [t1 ->] [t2 ->] /=.
by rewrite -Some_op Some_valid => /agree_op_invL' ->.
Qed.

Lemma correspondence_agreeL kI1 kI2 kR1 kR2 tI tR1 tR2 :
  correspondence kI1 kR1 tI tR1 -∗
  correspondence kI2 kR2 tI tR2 -∗
  ⌜kI1 = kI2 ∧ kR1 = kR2 ∧ tR1 = tR2⌝.
Proof.
iIntros "[H1 _] [H2 _]".
iPoseProof (session_frag_agree with "H1 H2") as "/= (_ & -> & -> & %Hdata)".
iPureIntro; do ![split => //].
by apply Some_inj; apply: Hdata; eauto.
Qed.

Lemma correspondence_agreeR kI1 kI2 kR1 kR2 tI1 tI2 tR :
  correspondence kI1 kR1 tI1 tR -∗
  correspondence kI2 kR2 tI2 tR -∗
  ⌜kI1 = kI2 ∧ kR1 = kR2 ∧ tI1 = tI2⌝.
Proof.
iIntros "[_ H1] [_ H2]".
iPoseProof (session_frag_agree with "H1 H2") as "/= (_ & -> & -> & %Hdata)".
iPureIntro; do ![split => //].
by apply Some_inj; apply: Hdata; eauto.
Qed.

Lemma correspondence_agreeLR kI1 kI2 kR1 kR2 t tI tR :
  correspondence kI1 kR1 t tR -∗
  correspondence kI2 kR2 tI t -∗
  False.
Proof.
iIntros "[H1 _] [_ H2]".
by iPoseProof (session_frag_agree with "H1 H2") as "/= (% & _)".
Qed.

Definition coherent_views t1 s1 : iProp :=
  match s1.(srole), s1.(sdata) with
  | Init, None => True
  | Init, Some t2 =>
    session_frag t2 (SessionData Resp s1.(sinit) s1.(sresp) (Some t1))
  | Resp, None => False
  | Resp, Some t2 =>
    session_frag t2 (SessionData Init s1.(sinit) s1.(sresp) None)
  end.

Global Instance coherent_views_persistent t1 s1 :
  Persistent (coherent_views t1 s1).
Proof.
rewrite /coherent_views; case: (srole s1) (sdata s1) => [] [?|] /=;
apply _.
Qed.

Definition session_map_inv SM : iProp :=
  ∀ t1 s1, ⌜SM !! t1 = Some s1⌝ -∗
    □ sinv s1.(srole) (sowner s1) (sother s1) t1
    ∗ crypto_meta t1 N ()
    ∗ coherent_views t1 s1.

Global Instance session_map_inv_persistent SM :
  Persistent (session_map_inv SM).
Proof. apply _. Qed.

Lemma session_map_inv_unregistered SM t :
  crypto_meta_token t (↑N) -∗
  session_map_inv SM -∗
  ⌜SM !! t = None⌝.
Proof.
iIntros "Hunreg Hinv".
destruct (SM !! t) as [s_t|] eqn:SM_t=> //.
iDestruct ("Hinv" $! _ _ SM_t) as "(?&Hreg&?)".
by iDestruct (crypto_meta_meta_token with "Hunreg Hreg") as "[]".
Qed.

Definition session_inv : iProp :=
  auth_inv γ to_session_map session_map_inv.

Definition session_ctx : iProp :=
  auth_ctx γ N to_session_map session_map_inv.

Lemma session_auth_session_frag E t s :
  ↑N ⊆ E →
  session_ctx -∗
  session_auth t s ={E}=∗
  session_auth t s ∗ session_frag t s.
Proof.
iIntros (?) "#ctx auth".
iMod (auth_acc to_session_map session_map_inv
        with "[ctx auth]") as (SM) "(%lb & inv & close)" => //; eauto.
iMod ("close" $! SM {[t := session_data_auth_frag s]} with "[inv]") as "own".
  iFrame; iPureIntro.
  case/singleton_included_l: lb => [x []].
  rewrite lookup_fmap option_equivE.
  case SM_t: (SM !! t) => [s'|] //= <-.
  rewrite Some_included_total session_data_auth_included => ?; subst s'.
  rewrite /session_data_auth_frag -singleton_op.
  apply: core_id_local_update.
  apply/singleton_included_l; exists (session_data_auth_frag s).
  rewrite lookup_fmap SM_t; split => //.
  rewrite Some_included_total; exists (session_data_auth s).
  by rewrite comm.
by rewrite /session_data_auth_frag -singleton_op auth_own_op.
Qed.

Lemma session_alloc_init kA kB tA E :
  ↑N ⊆ E →
  session_ctx -∗
  □ sinv Init kA kB tA -∗
  crypto_meta_token tA (↑N) ={E}=∗
  session_auth tA (SessionData Init kA kB None) ∗
  session_frag tA (SessionData Init kA kB None).
Proof.
iIntros (?) "#Hctx #Hsinv Hunreg".
set sA := SessionData Init kA kB None.
iMod (auth_empty γ) as "#Hinit".
iMod (auth_acc to_session_map session_map_inv
         with "[Hctx Hinit]") as "Hinv"; try by eauto.
iDestruct "Hinv" as (SM) "(_ & Hinv & Hclose)".
iAssert (▷ ⌜SM !! tA = None⌝)%I as "# > %Hfresh".
  iModIntro.
  by iApply (session_map_inv_unregistered with "[Hunreg] [Hinv]").
iMod (crypto_meta_set _ () with "Hunreg") as "#Hreg"; eauto.
rewrite -auth_own_op singleton_op.
iApply ("Hclose" $! (<[tA := sA]>SM)); iSplit.
  iPureIntro. rewrite /to_session_map fmap_insert.
  apply alloc_singleton_local_update.
    by rewrite lookup_fmap Hfresh.
  by apply session_data_valid.
iIntros "!>" (t1' s1').
case: (decide (tA = t1')) => [<-|ne].
  rewrite lookup_insert.
  iIntros (Hs); case: Hs=> {s1'}<-.
  by do 2![iSplit=> //].
by rewrite lookup_insert_ne //; iIntros (SM_t1').
Qed.

Lemma session_alloc_initG `{Decision G} kA kB tA E :
  ↑N ⊆ E →
  session_ctx -∗
  guarded G (□ sinv Init kA kB tA) -∗
  guarded G (crypto_meta_token tA (↑N)) ={E}=∗
  let s := SessionData Init kA kB None in
  guarded G (session_auth tA s ∗ session_frag tA s).
Proof.
iIntros (?) "#ctx #inv token".
rewrite /guarded; case: decide => // _.
by iApply session_alloc_init.
Qed.

Lemma session_alloc_resp kA kB tA tB E :
  ↑N ⊆ E →
  session_ctx -∗
  □ sinv Resp kB kA tB -∗
  session_frag tA (SessionData Init kA kB None) -∗
  crypto_meta_token tB (↑N) ={E}=∗
  session_auth tB (SessionData Resp kA kB (Some tA)) ∗
  session_frag tB (SessionData Resp kA kB (Some tA)).
Proof.
iIntros (?) "#Hctx #Hsinv #fragA Hunreg".
set sA := SessionData Init kA kB None.
set sB := SessionData Resp kA kB (Some tA).
iMod (auth_empty γ) as "#Hinit".
iMod (auth_acc to_session_map session_map_inv
         with "[Hctx Hinit]") as "Hinv"; try by eauto.
iDestruct "Hinv" as (SM) "(_ & Hinv & Hclose)".
iAssert (▷ ⌜SM !! tB = None⌝)%I as "# > %Hfresh".
  iModIntro.
  by iApply (session_map_inv_unregistered with "[Hunreg] [Hinv]").
iMod (crypto_meta_set _ () with "Hunreg") as "#Hreg"; eauto.
rewrite -auth_own_op singleton_op.
iApply ("Hclose" $! (<[tB := sB]>SM)); iSplit.
  iPureIntro. rewrite /to_session_map fmap_insert.
  apply alloc_singleton_local_update.
    by rewrite lookup_fmap Hfresh.
  by apply session_data_valid.
iIntros "!>" (t1' s1').
case: (decide (tB = t1')) => [<-|ne].
  rewrite lookup_insert.
  iIntros (Hs); case: Hs=> {s1'}<-.
  by do 2![iSplit=> //].
by rewrite lookup_insert_ne //; iIntros (SM_t1').
Qed.

Lemma session_alloc_respG `{Decision G} kA kB tA tB E :
  ↑N ⊆ E →
  session_ctx -∗
  guarded G (□ sinv Resp kB kA tB) -∗
  guarded G (session_frag tA (SessionData Init kA kB None)) -∗
  guarded G (crypto_meta_token tB (↑N)) ={E}=∗
  let s := SessionData Resp kA kB (Some tA) in
  guarded G (session_auth tB s ∗ session_frag tB s).
Proof.
iIntros (?) "#Hctx #Hsinv #Hfrag Hunreg".
rewrite /guarded; case: decide => //= _.
by iApply session_alloc_resp.
Qed.

Lemma session_map_auth_included t s SM :
  {[t := session_data_auth s]} ≼ to_session_map SM ↔
  SM !! t = Some s.
Proof.
split.
- move=> e; apply/leibniz_equiv.
  case/singleton_included_l: e=> x [].
  rewrite lookup_fmap option_equivE.
  case: (SM !! t)=> [s'|] //= <-.
  rewrite Some_included; case.
  + by case=> /= _; rewrite option_equivE.
  + by rewrite session_data_auth_included=> <-.
- move=> e; apply/singleton_included_l.
  exists (session_data_auth_frag s).
  by rewrite lookup_fmap e /= Some_included session_data_auth_included; eauto.
Qed.

Lemma session_map_frag_included t s SM :
  {[t := session_data_frag s]} ≼ to_session_map SM ↔
  ∃ s', SM !! t = Some s' ∧ to_session_data' s ≼ to_session_data' s'.
Proof.
split.
- case/singleton_included_l=> x [].
  rewrite lookup_fmap option_equivE.
  case: (SM !! t)=> [s'|] //= <-.
  rewrite Some_included; case.
  + by case=> /=; rewrite option_equivE.
  + rewrite session_data_frag_included; eauto.
- case=> s' [H1 H2].
  apply/singleton_included_l.
  rewrite lookup_fmap H1 /=.
  exists (session_data_auth_frag s'); split=> //.
  by rewrite Some_included session_data_frag_included; right.
Qed.

Lemma session_frag_inv E t s :
  ↑N ⊆ E →
  session_ctx -∗
  session_frag t s ={E}=∗
  ▷ □ sinv (srole s) (sowner s) (sother s) t ∗
  ▷ (⌜is_Some (sdata s)⌝ → coherent_views t s).
Proof.
move=> sub; iIntros "#Hctx Hterm".
iMod (auth_acc to_session_map _ _ _ _ {[t := session_data_frag s]}
         with "[Hctx Hterm]") as "Hinv"; try by eauto.
iDestruct "Hinv" as (SM) "(%Hincl & #Hinv & Hclose)".
iMod ("Hclose" $! SM {[t := session_data_frag s]} with "[Hinv]").
  by eauto.
case/session_map_frag_included: Hincl=> s' [SM_t ss'].
iModIntro.
rewrite /sowner /sother /coherent_views.
case/to_session_data'_included: ss'=> -> [-> [-> e]].
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

Arguments sroleo !_ /.
Arguments sother !_ /.
Arguments sowner !_ /.

Lemma session_update kA kB tA tB E :
  ↑N ⊆ E →
  session_ctx -∗
  session_auth tA (SessionData Init kA kB None) -∗
  session_frag tB (SessionData Resp kA kB (Some tA)) ={E}=∗
  session_auth tA (SessionData Init kA kB (Some tB)) ∗
  session_frag tA (SessionData Init kA kB (Some tB)).
Proof.
iIntros (sub) "#Hctx HA #HB".
case: (decide (tA = tB))=> [<-|tAB].
  iPoseProof (session_auth_frag_agree with "HA HB") as "%agree".
  by rewrite to_session_data'_included /= in agree *; intuition.
set s1 := SessionData Init _ _ _; set s2 := SessionData Resp _ _ _.
pose (f1 := {[tA := session_data_auth s1]} : gmap _ _).
pose (f2 := {[tB := session_data_frag s2]} : gmap _ _).
iMod (auth_acc to_session_map session_map_inv with "[Hctx HA]")
    as "Hinv"; try by try iClear "HB"; eauto.
iDestruct "Hinv" as (SM) "(%SM_tA & #Hinv & Hclose)".
move/session_map_auth_included in SM_tA.
set s1' := SessionData Init kA kB (Some tB).
pose (f1' := {[tA := session_data_auth_frag s1']} : gmap _ _).
pose (SM' := <[tA := s1']> SM).
iMod ("Hclose" $! (<[tA := s1']>SM) f1' with "[]") as "Hown"; last first.
  rewrite /f1' -singleton_op !auth_own_op; iModIntro.
  by iDestruct "Hown" as "[??]"; iFrame.
iSplit.
  iPureIntro.
  rewrite /to_session_map fmap_insert //.
  apply: singleton_local_update; first by rewrite lookup_fmap SM_tA.
  apply local_update_unital_discrete.
  intros a _ <-%cancelable=> //; last by apply _.
  split=> //; first exact: session_data_auth_frag_valid.
  rewrite {2}/session_data_auth_frag -cmra_assoc -auth_frag_op -Some_op.
  by rewrite /to_session_data' /= -!pair_op !agree_idemp.
iIntros "!>" (t s).
case: (decide (tA = t))=> [<-|ne].
  rewrite lookup_insert; iIntros (e); case: e=> ?; subst s.
  iDestruct ("Hinv" $! _ _ SM_tA) as "(?&?&?)".
  by do 2![iSplit=> //=].
by rewrite lookup_insert_ne //.
Qed.

Lemma session_updateG `{Decision G} kA kB tA tB E :
  ↑N ⊆ E →
  session_ctx -∗
  guarded G (session_auth tA (SessionData Init kA kB None)) -∗
  guarded G (session_frag tB (SessionData Resp kA kB (Some tA))) ={E}=∗
  let s := SessionData Init kA kB (Some tB) in
  guarded G (session_auth tA s ∗ session_frag tA s).
Proof.
iIntros (?) "#ctx H1 #H2"; rewrite /guarded; case: decide => //= _.
by iApply (session_update with "ctx H1 H2").
Qed.

End Session.

Arguments sessionG : clear implicits.
