From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl namespace_map frac.
From iris.base_logic.lib Require Import auth.
From iris.heap_lang Require Import notation proofmode.
From crypto Require Import lib term crypto primitives tactics.

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
Implicit Types lvl : level.

Definition session_mapUR :=
  gmapUR term (authR (optionUR session_data'R)).

Class sessionG := {
  session_inG  :> inG Σ (authR session_mapUR);
  session_name :  gname;
  key_inv      :  role → term → iProp;
  key_inv_persistent :> ∀ rl t, Persistent (key_inv rl t);
  sessionN     :  namespace;
}.

Context `{!sessionG}.

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
  auth_own session_name {[t := session_data_auth s]}.

Definition session_frag t s : iProp :=
  auth_own session_name {[t := session_data_frag s]}.

Global Instance session_frag_persistent t s :
  Persistent (session_frag t s).
Proof. apply _. Qed.

Lemma session_agree t s1 s2 :
  session_auth t s1 -∗
  session_frag t s2 -∗
  ⌜to_session_data' s2 ≼ to_session_data' s1⌝.
Proof.
iIntros "Hown1 Hown2".
iPoseProof (own_valid_2 with "Hown1 Hown2") as "%Hvalid".
iPureIntro; apply/session_data_valid.
by rewrite auth_valid_discrete /= singleton_op singleton_valid in Hvalid *.
Qed.

Definition coherent_views SM t1 s1 : Prop :=
  match s1.(srole), s1.(sdata) with
  | Init, None => True
  | Init, Some t2 =>
    SM !! t2 = Some (SessionData Resp s1.(sinit) s1.(sresp) (Some t1))
  | Resp, None => False
  | Resp, Some _ => True
  end.

Definition session_map_inv SM : iProp :=
  ∀ t1 s1, ⌜SM !! t1 = Some s1⌝ -∗
    key_inv s1.(srole) (sowner s1)
    ∗ key_inv (sroleo s1) (sother s1)
    ∗ crypto_meta t1 sessionN ()
    ∗ stermT Sec t1
    ∗ (if sdata s1 is Some t2 then stermT Sec t2 else True)
    ∗ ⌜coherent_views SM t1 s1⌝.

Global Instance session_map_inv_persistent SM :
  Persistent (session_map_inv SM).
Proof. apply _. Qed.

Lemma session_map_inv_unregistered SM t :
  crypto_meta_token t (↑sessionN) -∗
  session_map_inv SM -∗
  ⌜SM !! t = None⌝.
Proof.
iIntros "Hunreg Hinv".
destruct (SM !! t) as [s_t|] eqn:SM_t=> //.
iDestruct ("Hinv" $! _ _ SM_t) as "(?&?&Hreg&?)".
by iDestruct (crypto_meta_meta_token with "Hunreg Hreg") as "[]".
Qed.

Definition session_inv : iProp :=
  auth_inv session_name to_session_map session_map_inv.

Definition session_ctx : iProp :=
  auth_ctx session_name sessionN to_session_map session_map_inv.

Lemma session_alloc lvl kI kR t rl E ot :
  let kA := if rl is Init then kI else kR in
  let kB := if rl is Init then kR else kI in
  let s  := SessionData rl kI kR ot       in
  ↑sessionN ⊆ E →
  (if rl is Init then ot = None else is_Some ot) →
  session_ctx -∗
  key_inv rl kA -∗
  crypto_meta_token t (↑sessionN) -∗
  termT Pub (TKey Enc kB) -∗
  guarded lvl (key_inv (swap_role rl) kB) -∗
  stermT lvl t -∗
  (if ot is Some t' then stermT lvl t' else True) ={E}=∗
  guarded lvl (session_auth t s ∗ session_frag t s).
Proof.
move=> kA kB s sub rl_ot; iIntros "#Hctx #Howner Hunreg #HkB #HkB' #Ht #Ht'".
case: lvl => //=.
iMod (auth_empty session_name) as "#Hinit".
iMod (auth_acc to_session_map session_map_inv
         with "[Hctx Hinit]") as "Hinv"; try by eauto.
iDestruct "Hinv" as (SM) "(_ & Hinv & Hclose)".
iAssert (▷ ⌜SM !! t = None⌝)%I as "# > %Hfresh".
  iModIntro.
  by iApply (session_map_inv_unregistered with "[Hunreg] [Hinv]").
iMod (crypto_meta_set _ () with "Hunreg") as "#Hreg"; eauto.
rewrite -auth_own_op singleton_op.
iApply ("Hclose" $! (<[t:=s]>SM)); iSplit.
  iPureIntro. rewrite /to_session_map fmap_insert.
  apply alloc_singleton_local_update.
    by rewrite lookup_fmap Hfresh.
  by apply session_data_valid.
iIntros "!>" (t1' s1').
case: (decide (t = t1')) => [<-|ne].
  rewrite lookup_insert.
  iIntros (Hs); case: Hs=> {s1'}<-.
  do 5![iSplit=> //].
  rewrite /s; case: (rl) rl_ot=> // rl_ot.
    by rewrite rl_ot.
  by case: rl_ot=> t' -> /=.
rewrite lookup_insert_ne //; iIntros (SM_t1').
iDestruct ("Hinv" $! _ _ SM_t1') as "(? & ? & ? & ? & ? & %Hcoh)".
iFrame; iPureIntro.
move: Hcoh; rewrite /coherent_views.
case: (srole s1') (sdata s1')=> [|] [t2'|] //.
case: (decide (t = t2'))=> [<-|?]; first by rewrite Hfresh.
by rewrite lookup_insert_ne.
Qed.

Lemma session_alloc_init lvl kA kB tA E :
  ↑sessionN ⊆ E →
  session_ctx -∗
  key_inv Init kA -∗
  crypto_meta_token tA (↑sessionN) -∗
  termT Pub (TKey Enc kB) -∗
  guarded lvl (key_inv Resp kB) -∗
  stermT lvl tA ={E}=∗
  guarded lvl (session_auth tA (SessionData Init kA kB None) ∗
               session_frag tA (SessionData Init kA kB None)).
Proof.
iIntros (HE) "#Hctx #HkA Hunreg #HkB #HkB' #HtA".
by iApply (session_alloc with "Hctx HkA Hunreg HkB HkB' HtA").
Qed.

Lemma session_alloc_resp lvl kA kB tA tB E :
  ↑sessionN ⊆ E →
  session_ctx -∗
  key_inv Resp kB -∗
  crypto_meta_token tB (↑sessionN) -∗
  termT Pub (TKey Enc kA) -∗
  guarded lvl (key_inv Init kA) -∗
  stermT lvl tB -∗
  stermT lvl tA ={E}=∗
  guarded lvl (session_auth tB (SessionData Resp kA kB (Some tA)) ∗
               session_frag tB (SessionData Resp kA kB (Some tA))).
Proof.
iIntros (?) "#Hctx #HkB Hunreg #HkA #HkA' #HtB #HtA".
by iApply (session_alloc with "Hctx HkB Hunreg HkA HkA' HtB")=> /=; eauto.
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

Lemma session_key_inv E lvl t s :
  ↑sessionN ⊆ E →
  session_ctx -∗
  guarded lvl (session_frag t s) ={E}=∗
  ▷ guarded lvl (key_inv s.(srole) (sowner s)).
Proof.
move=> sub; iIntros "#Hctx Hterm"; case: lvl => //=.
iMod (auth_acc to_session_map _ _ _ _ {[t := session_data_frag s]}
         with "[Hctx Hterm]") as "Hinv"; try by eauto.
iDestruct "Hinv" as (SM) "(%Hincl & Hinv & Hclose)".
iAssert (▷ key_inv s.(srole) (sowner s))%I with "[Hinv]" as "#Hs".
  case/session_map_frag_included: Hincl=> s' [SM_t ss'].
  iModIntro.
  rewrite /sowner; case/to_session_data'_included: ss'=> -> [-> [-> _]].
  by iDestruct ("Hinv" $! _ _ SM_t) as "(?&?&?&?&?&?)".
by iMod ("Hclose" $! SM {[t := session_data_frag s]} with "[Hinv]"); eauto.
Qed.

Definition session_inv' t1 s1 : iProp :=
  key_inv s1.(srole) (sowner s1)
  ∗ key_inv (sroleo s1) (sother s1)
  ∗ crypto_meta t1 sessionN ()
  ∗ stermT Sec t1
  ∗ (if sdata s1 is Some t2 then stermT Sec t2 else True).

Lemma session_frag_session_inv0 E lvl t s :
  ↑sessionN ⊆ E →
  session_ctx -∗
  guarded lvl (session_frag t s) ={E}=∗
  ∃ s', ⌜to_session_data' s ≼ to_session_data' s'⌝ ∗
        ▷ guarded lvl (session_inv' t s').
Proof.
move=> sub; iIntros "#Hctx Hterm"; case: lvl => //=.
  by iExists s.
iMod (auth_acc to_session_map session_map_inv
         with "[Hctx Hterm]") as "Hinv"; try by eauto.
iDestruct "Hinv" as (SM) "(%Hincl & #Hinv & Hclose)".
case/session_map_frag_included: Hincl=> s' [SM_t ss'].
iExists s'.
iAssert (▷ session_inv' t s')%I with "[Hinv]" as "#Hs".
  iModIntro.
  iDestruct ("Hinv" $! _ _ SM_t) as "(?&?&?&?&?&?)".
  by iSplit => //; eauto.
by iMod ("Hclose" $! SM {[t := session_data_frag s]} with "[Hinv]"); eauto.
Qed.

Lemma session_frag_session_inv1 E lvl rl kA kB t t' :
  ↑sessionN ⊆ E →
  let s := SessionData rl kA kB (Some t') in
  session_ctx -∗
  guarded lvl (session_frag t s) ={E}=∗
  ▷ guarded lvl (session_inv' t s).
Proof.
move=> sub s; iIntros "#Hctx #Hterm".
iMod (session_frag_session_inv0 with "Hctx Hterm") as (s') "[%s_s' Hs']" => //.
do 2!iModIntro.
rewrite /session_inv' /sowner /sother /sroleo /=.
by case/to_session_data'_included: s_s' => <- [] <- [] <- <- /=.
Qed.

(* TODO: rename *)
Lemma session_frag_session_inv2 E lvl t s :
  ↑sessionN ⊆ E →
  session_ctx -∗
  termT lvl t -∗
  guarded lvl (session_frag t s) ={E}=∗
  ▷ stermT lvl t.
Proof.
iIntros (sub) "#Hctx #Ht #Hsess".
iMod (session_frag_session_inv0 with "Hctx Hsess") as (s') "[%s_s' Hs']" => //.
iDestruct "Hs'" as "(_&_&_&#Ht'&_)".
by case: lvl=> //=; do 2!iModIntro; iSplit; eauto.
Qed.

Lemma session_frag_key_inv E lvl t s :
  ↑sessionN ⊆ E →
  session_ctx -∗
  guarded lvl (session_frag t s) ={E}=∗
  ▷ guarded lvl (key_inv (srole s) (sowner s)).
Proof.
iIntros (sub) "#Hctx #Hsess".
iMod (session_frag_session_inv0 with "Hctx Hsess") as (s') "[%s_s' Hs']" => //.
iDestruct "Hs'" as "(#Hk&_)".
case: lvl=> //=; do 2!iModIntro.
rewrite /sowner.
by case/to_session_data'_included: s_s' => [] <- [] <- [] <- _.
Qed.

Arguments sroleo !_ /.
Arguments sother !_ /.
Arguments sowner !_ /.

Lemma session_update lvl kA kB tA tB E :
  ↑sessionN ⊆ E →
  session_ctx -∗
  guarded lvl (session_auth tA (SessionData Init kA kB None)) -∗
  guarded lvl (session_frag tB (SessionData Resp kA kB (Some tA))) ={E}=∗
  guarded lvl (session_auth tA (SessionData Init kA kB (Some tB)) ∗
               session_frag tA (SessionData Init kA kB (Some tB))).
Proof.
iIntros (sub) "Hctx HA HB"; case: lvl => //=.
case: (decide (tA = tB))=> [<-|tAB].
  iPoseProof (session_agree with "HA HB") as "%agree".
  by rewrite to_session_data'_included /= in agree *; intuition.
set s1 := SessionData Init _ _ _; set s2 := SessionData Resp _ _ _.
pose (f1 := {[tA := session_data_auth s1]} : gmap _ _).
pose (f2 := {[tB := session_data_frag s2]} : gmap _ _).
iMod (auth_acc to_session_map _ _ _ _
         (f1 ⋅ f2) with "[Hctx HA HB]") as "Hinv"; try by eauto.
  by rewrite auth_own_op; iFrame.
iDestruct "Hinv" as (SM) "(%Hincl & #Hinv & Hclose)".
have /session_map_auth_included SM_tA : f1 ≼ to_session_map SM.
  apply: cmra_included_trans Hincl; exact: cmra_included_l.
have /session_map_frag_included SM_tB: f2 ≼ to_session_map SM.
  apply: cmra_included_trans Hincl; exact: cmra_included_r.
case: SM_tB=> s2' [SM_tB s2_incl].
move: SM_tB; rewrite -(to_session_data'_included_eq s2_incl) /=; last by eauto.
move=> SM_tB {s2' s2_incl}.
set s1' := SessionData Init kA kB (Some tB).
pose (f1' := {[tA := session_data_auth_frag s1']} : gmap _ _).
pose (SM' := <[tA := s1']> SM).
iMod ("Hclose" $! (<[tA := s1']>SM) (f1' ⋅ f2) with "[]") as "Hown"; last first.
  rewrite /f1' -singleton_op !auth_own_op; iModIntro.
  by iDestruct "Hown" as "[[??]?]"; iFrame.
have f2_tA : f2 !! tA = None by rewrite lookup_singleton_ne.
iSplit.
  iPureIntro.
  rewrite /to_session_map fmap_insert -![_ ⋅ f2]insert_singleton_op //.
  rewrite -(insert_insert f2 tA (session_data_auth_frag s1') (session_data_auth s1)).
  eapply insert_local_update.
  - by rewrite lookup_fmap SM_tA.
  - by rewrite lookup_insert.
  apply local_update_unital_discrete.
  intros a _ <-%cancelable=> //; last by apply _.
  split=> //; first exact: session_data_auth_frag_valid.
  rewrite {2}/session_data_auth_frag -cmra_assoc -auth_frag_op -Some_op.
  by rewrite /to_session_data' /= -!pair_op !agree_idemp.
iIntros "!>" (t s).
case: (decide (tA = t))=> [<-|ne].
  rewrite lookup_insert; iIntros (e); case: e=> ?; subst s.
  iDestruct ("Hinv" $! _ _ SM_tA) as "(?&?&?&?&?&?)".
  iDestruct ("Hinv" $! _ _ SM_tB) as "(?&?&?&?&?&?)".
  do 5![iSplit=> //]; iPureIntro.
  rewrite /s1' /=.
  by rewrite /coherent_views /= lookup_insert_ne // SM_tB.
rewrite lookup_insert_ne //.
iIntros "%SM_t"; iDestruct ("Hinv" $! _ _ SM_t) as "(?&?&?&?&?&%Hcoh)".
do 5![iSplit=> //]; iPureIntro.
move: Hcoh; rewrite /coherent_views.
case erole: (srole s)=> //.
case edata: (sdata s)=> [t'|] //.
case: (decide (tA = t'))=> [<-|?]; first by rewrite SM_tA.
by rewrite lookup_insert_ne.
Qed.

End Session.
