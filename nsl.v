From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl namespace_map frac.
From iris.base_logic.lib Require Import auth.
From iris.heap_lang Require Import notation proofmode.
From crypto Require Import lib term crypto1 primitives tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma option_Forall2E {A B} {R : A → B → Prop} ox oy :
  option_Forall2 R ox oy ↔
  match ox, oy with
  | Some x, Some y => R x y
  | None, None => True
  | _, _ => False
  end.
Proof.
split; first by case.
by case: ox oy=> [x|] [y|] //; constructor.
Qed.

Lemma option_equivE `{Equiv A} (ox oy : option A) :
  ox ≡ oy ↔
  match ox, oy with
  | Some x, Some y => x ≡ y
  | None, None => True
  | _, _ => False
  end.
Proof. apply option_Forall2E. Qed.

Lemma namespace_map_validI Σ (A : cmraT) (x : namespace_map A) :
  ✓ x ⊣⊢@{iPropI Σ}
  match namespace_map_token_proj x with
  | CoPset E =>
    ✓ namespace_map_data_proj x
    ∧ ⌜∀ i, namespace_map_data_proj x !! i = None ∨ i ∉ E⌝
  | CoPsetBot => False
  end.
Proof. by uPred.unseal; case: x=> [? [?|]]. Qed.

Lemma meta_contra `{Countable L, !gen_heapG L V Σ, Countable A} l (x : A) N E :
  ↑N ⊆ E →
  meta_token l E -∗
  meta l N x -∗
  False.
Proof.
iIntros (sub) "Htoken #Hmeta1".
pose (X := {[encode x]} : gset positive).
iMod (meta_set _ _ (fresh X) with "Htoken") as "#Hmeta2"=> //.
iAssert (meta l N (encode x)) as "Hmeta1'".
  by rewrite {1 3}/meta seal_eq.
iPoseProof (meta_agree with "Hmeta1' Hmeta2") as "%e"; iPureIntro.
assert (contra : encode x ∈ X). { by apply/elem_of_singleton. }
destruct (is_fresh X); by rewrite -e.
Qed.

Global Instance auth_auth_cancelable (T : ucmraT) (x : T) : Cancelable (● x).
Proof.
intros n [yauth yfrag] [zauth zfrag].
rewrite auth_validN_eq /=; destruct yauth as [[yfrac yauth]|]; rewrite /=.
  destruct 1 as [contra _].
  apply exclusiveN_l in contra; first by destruct contra.
  exact frac_full_exclusive. (* ??? *)
destruct 1 as [_ (x' & ex & dec & valid)].
destruct 1 as [eauth efrag]; simpl in *.
rewrite !ucmra_unit_left_id in efrag *; move=> efrag.
split=> //.
destruct zauth as [[zfrac zauth]|]; trivial.
rewrite ucmra_unit_right_id -Some_op -pair_op in eauth * => eauth.
move/Some_dist_inj: eauth=> [/= eauth _].
enough (contra : ✓ (1%Qp ⋅ zfrac)).
  apply exclusive_l in contra; first by case: contra.
  apply frac_full_exclusive.
by rewrite -eauth.
Qed.

(* Double-check this does not exist *)
Lemma singleton_inj `{!EqDecision T, !Countable T} :
  Inj eq eq (singleton : T -> gset T).
Proof.
move=> x1 x2 e.
have : x1 ∈ ({[x1]} : gset _) by apply elem_of_singleton.
by rewrite e => /elem_of_singleton.
Qed.

Section NSL.

Context `{!resG Σ, !heapG Σ}.

Inductive role := Init | Resp.

Canonical roleO := leibnizO role.

Implicit Types rl : role.

Global Instance role_inhabited : Inhabited role := populate Init.

Lemma role_equivI rl1 rl2 :
  rl1 ≡ rl2 ⊣⊢@{iPropI Σ}
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

Inductive session := Session {
  srole : role;
  sinit : loc;
  sresp : loc;
  sdata : option term;
}.

Canonical sessionO := leibnizO session.

Global Instance session_inhabited : Inhabited session :=
  populate (Session inhabitant inhabitant inhabitant inhabitant).

Definition sroleo s := swap_role s.(srole).

Definition sowner s :=
  if s.(srole) is Init then s.(sinit) else s.(sresp).

Definition sother s :=
  if s.(srole) is Init then s.(sresp) else s.(sinit).

Definition sessionR : cmraT :=
  prodR (prodR (prodR (agreeR roleO) (agreeR locO)) (agreeR locO))
        (optionR (agreeR termO)).

Implicit Types t : term.
Implicit Types SM : gmap term session.
Implicit Types s : session.
Implicit Types lvl : level.

Class nslG := {
  in_nsl_sessG :> inG Σ (authR (gmapUR term (authR (optionUR sessionR))));
  nsl_sess_name : gname;
  nsl_init_name : gname;
  nsl_resp_name : gname;
}.

Context `{!tagG Σ, !nslG}.

Global Instance nslG_authG : authG _ _ :=
  AuthG Σ (gmapUR term (authR (optionUR sessionR))) in_nsl_sessG _.

Definition to_session s : sessionR :=
  (to_agree s.(srole), to_agree s.(sinit),
   to_agree s.(sresp), to_agree <$> s.(sdata)).

Global Instance to_session_inj : Inj (=) (≡) to_session.
Proof.
case=> [??? ot1] [??? ot2]; do 3![case]=> /=.
do 3![move=> /to_agree_inj ->].
case: ot2=> [t2|] /=; last first.
  by move=> /equiv_None; case: ot1.
case/fmap_Some_equiv=> t1 [-> /to_agree_inj e].
by apply leibniz_equiv in e; congruence.
Qed.

Lemma to_session_valid s : ✓ to_session s.
Proof.
rewrite /to_session; repeat split=> //=.
by case: (sdata s).
Qed.

Lemma to_session_validN n s : ✓{n} to_session s.
Proof.
rewrite /to_session; repeat split=> //=.
by case: (sdata s).
Qed.

Lemma to_session_included s1 s2 :
  to_session s1 ≼ to_session s2 ↔
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

Lemma to_session_included_eq s1 s2 :
  to_session s1 ≼ to_session s2 →
  is_Some s1.(sdata) →
  s1 = s2.
Proof.
move=> eincl [t e].
case: s1 s2 e eincl => [????] [????] /= ->.
rewrite to_session_included /=.
by case=> <- [<- [<- <-]].
Qed.

Definition session_auth s := ● (Some (to_session s)).
Definition session_frag s := ◯ (Some (to_session s)).
Definition session_auth_frag s :=
  session_auth s ⋅ session_frag s.

Lemma session_auth_included s1 s2 :
  session_auth s1 ≼ session_auth_frag s2 ↔ s1 = s2.
Proof.
split; last by move=> ->; exists (session_frag s2).
rewrite auth_included /= Some_included.
destruct 1 as [[[_ e]|e] _].
- rewrite /= in e.
  apply to_agree_inj in e.
  apply Some_equiv_inj in e.
  by apply to_session_inj in e.
- move: e; rewrite pair_included; case=> _.
  rewrite to_agree_included=> e.
  by apply Some_equiv_inj, to_session_inj in e.
Qed.

Lemma session_frag_included s1 s2 :
  session_frag s1 ≼ session_auth_frag s2 ↔
  to_session s1 ≼ to_session s2.
Proof.
split.
- rewrite auth_included.
  case=> _ /=; rewrite ucmra_unit_left_id.
  by rewrite Some_included; case=> [->|].
- move=> e; transitivity (session_frag s2).
    by rewrite auth_included /= Some_included; eauto.
  by exists (session_auth s2); rewrite cmra_comm.
Qed.

Lemma session_auth_valid s : ✓ session_auth s.
Proof.
rewrite auth_valid_eq /=; split=> // n.
exists (Some (to_session s)); split=> //.
split.
- by exists (Some (to_session s)); rewrite ucmra_unit_left_id.
- apply Some_validN, to_session_validN.
Qed.

Lemma session_frag_valid s : ✓ session_frag s.
Proof. by apply auth_frag_valid, to_session_valid. Qed.

Lemma session_valid s1 s2 :
  ✓ (session_auth s1 ⋅ session_frag s2) ↔
  to_session s2 ≼ to_session s1.
Proof.
rewrite auth_both_valid Some_included; split.
- by case=> [[->|?] _].
- move=> e; intuition eauto.
  rewrite Some_valid; exact: to_session_valid.
Qed.

Lemma session_auth_frag_valid s : ✓ session_auth_frag s.
Proof. exact/session_valid. Qed.

Definition to_session_map SM : gmap term _ :=
  session_auth_frag <$> SM.

Definition term_session_auth t s : iProp Σ :=
  auth_own nsl_sess_name {[t := session_auth s]}.

Definition term_session_frag t s : iProp Σ :=
  auth_own nsl_sess_name {[t := session_frag s]}.

Global Instance term_session_persistent t s :
  Persistent (term_session_frag t s).
Proof. apply _. Qed.

Lemma term_session_agree t s1 s2 :
  term_session_auth t s1 -∗
  term_session_frag t s2 -∗
  ⌜to_session s2 ≼ to_session s1⌝.
Proof.
iIntros "Hown1 Hown2".
iPoseProof (own_valid_2 with "Hown1 Hown2") as "%Hvalid".
iPureIntro; apply/session_valid.
by rewrite auth_valid_discrete /= singleton_op singleton_valid in Hvalid *.
Qed.

Definition msg1_spec nA pkA :=
  TPair (TInt 1) (TPair nA (TPair pkA (TInt 0))).

Definition msg1_pred p : iProp Σ :=
  ∃ nA kA, ⌜p.2 = Spec.of_list [nA; TKey KAEnc kA]⌝ ∗
           term_session_frag nA (Session Init kA p.1 None).

Global Instance msg1_pred_proper : NonExpansive msg1_pred.
Proof.
move=> n; case=> [??] [??] [/= ??]; solve_contractive.
Qed.

Global Instance msg1_pred_persistent p : Persistent (msg1_pred p).
Proof. apply _. Qed.

Definition msg2_pred p : iProp Σ :=
  ∃ nA nB kB,
    ⌜p.2 = Spec.of_list [nA; nB; TKey KAEnc kB]⌝ ∗
    term_session_frag nB (Session Resp p.1 kB (Some nA)).

Global Instance msg2_pred_proper : NonExpansive msg2_pred.
Proof.
move=> n; case=> [??] [??] [/= ??].
solve_contractive.
Qed.

Global Instance msg2_pred_persistent p :
  Persistent (msg2_pred p).
Proof.
case: p=> kA t.
case: t; try by move=> *; apply _.
Qed.

Definition msg3_pred p : iProp Σ :=
  ∃ nA kA,
    term_session_frag nA (Session Init kA p.1 (Some p.2)) ∗
    term_session_frag p.2 (Session Resp kA p.1 (Some nA)).

Global Instance msg3_pred_proper : NonExpansive msg3_pred.
Proof.
move=> n; case=> [??] [??] [/= ??].
solve_contractive.
Qed.

Global Instance msg3_pred_persistent p : Persistent (msg3_pred p).
Proof. apply _. Qed.

Definition unregistered t : iProp Σ :=
  ∃ l, ⌜symbols_of_term t = {[l]}⌝
       ∗ meta_token l (↑cryptoN.@"nsl".@"secret").

Definition registered t : iProp Σ :=
  ∃ l, ⌜symbols_of_term t = {[l]}⌝
       ∗ meta l (cryptoN.@"nsl".@"secret") ().

Lemma registered_unregistered t :
  registered t -∗
  unregistered t -∗
  False.
Proof.
iDestruct 1 as (l1) "[%Hl1 Hmeta1]".
iDestruct 1 as (l2) "[%Hl2 Hmeta2]".
move: Hl1; rewrite Hl2 => e; rewrite (singleton_inj e).
by iApply (meta_contra with "Hmeta2 Hmeta1").
Qed.

Lemma registered_set t :
  unregistered t ==∗
  registered t.
Proof.
iDestruct 1 as (l) "[%t_l Hmeta]".
iMod (meta_set _ _ () with "Hmeta") as "#Hmeta"; eauto.
by iModIntro; iExists l; iSplit.
Qed.

Global Instance registered_persistent t :
  Persistent (registered t).
Proof. apply _. Qed.

Global Instance registered_timeless t :
  Timeless (registered t).
Proof. apply _. Qed.

Definition role_name rl : gname :=
  if rl is Init then nsl_init_name else nsl_resp_name.

Definition nsl_key rl k : iProp Σ :=
  akeyT Pub Sec (OfeMor tagged_inv) k ∗
  match rl with
  | Init =>
    own_tag k "m2" (OfeMor msg2_pred)
  | Resp =>
    own_tag k "m1" (OfeMor msg1_pred) ∗
    own_tag k "m3" (OfeMor msg3_pred)
  end.

Global Instance nsl_key_persistent rl k :
  Persistent (nsl_key rl k).
Proof. rewrite /nsl_key; case: rl; apply _. Qed.

Definition coherent_views SM t1 s1 : Prop :=
  match s1.(srole), s1.(sdata) with
  | Init, None => True
  | Init, Some t2 =>
    SM !! t2 = Some (Session Resp s1.(sinit) s1.(sresp) (Some t1))
  | Resp, None => False
  | Resp, Some _ => True
  end.

Definition session_inv SM : iProp Σ :=
  ∀ t1 s1, ⌜SM !! t1 = Some s1⌝ -∗
    nsl_key s1.(srole) (sowner s1)
    ∗ nsl_key (sroleo s1) (sother s1)
    ∗ registered t1
    ∗ stermT Sec t1
    ∗ (if sdata s1 is Some t2 then stermT Sec t2 else True)
    ∗ ⌜coherent_views SM t1 s1⌝.

Global Instance session_inv_persistent SM : Persistent (session_inv SM).
Proof. apply _. Qed.

Lemma session_inv_unregistered SM t :
  unregistered t -∗
  session_inv SM -∗
  ⌜SM !! t = None⌝.
Proof.
iIntros "Hunreg Hinv".
destruct (SM !! t) as [s_t|] eqn:SM_t=> //.
iDestruct ("Hinv" $! _ _ SM_t) as "(?&?&Hreg&?)".
by iDestruct (registered_unregistered with "Hreg Hunreg") as "[]".
Qed.

Definition nsl_inv : iProp Σ :=
  auth_inv nsl_sess_name to_session_map session_inv.

Definition nsl_ctx : iProp Σ :=
  auth_ctx nsl_sess_name (cryptoN.@"nsl") to_session_map session_inv.

Lemma nsl_sess_alloc lvl kI kR t rl E ot :
  let kA := if rl is Init then kI else kR in
  let kB := if rl is Init then kR else kI in
  let s  := Session rl kI kR ot           in
  ↑cryptoN.@"nsl" ⊆ E →
  (if rl is Init then ot = None else is_Some ot) →
  nsl_ctx -∗
  nsl_key rl kA -∗
  unregistered t -∗
  pub_enc_key kB -∗
  guarded lvl (nsl_key (swap_role rl) kB) -∗
  stermT lvl t -∗
  (if ot is Some t' then stermT lvl t' else True) ={E}=∗
  guarded lvl (term_session_auth t s ∗ term_session_frag t s).
Proof.
move=> kA kB s sub rl_ot; iIntros "#Hctx #Howner Hunreg #HkB #HkB' #Ht #Ht'".
case: lvl => //=.
iMod (auth_empty nsl_sess_name) as "#Hinit".
(* FIXME Why do I have to provide this instance? *)
iMod (auth_acc to_session_map _ _ _ _ ε
         with "[Hctx Hinit]") as "Hinv"; try by eauto.
iDestruct "Hinv" as (SM) "(_ & Hinv & Hclose)".
iAssert (▷ ⌜SM !! t = None⌝)%I as "# > %Hfresh".
  iModIntro.
  by iApply (session_inv_unregistered with "[Hunreg] [Hinv]").
iMod (registered_set with "Hunreg") as "#Hreg"; eauto.
rewrite -auth_own_op singleton_op.
iApply ("Hclose" $! (<[t:=s]>SM)); iSplit.
  iPureIntro. rewrite /to_session_map fmap_insert.
  apply alloc_singleton_local_update.
    by rewrite lookup_fmap Hfresh.
  by apply session_valid.
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

Lemma nsl_sess_alloc_init lvl kA kB tA E :
  ↑cryptoN.@"nsl" ⊆ E →
  nsl_ctx -∗
  nsl_key Init kA -∗
  unregistered tA -∗
  pub_enc_key kB -∗
  guarded lvl (nsl_key Resp kB) -∗
  stermT lvl tA ={E}=∗
  guarded lvl (term_session_auth tA (Session Init kA kB None) ∗
               term_session_frag tA (Session Init kA kB None)).
Proof.
iIntros (HE) "#Hctx #HkA Hunreg #HkB #HkB' #HtA".
by iApply (nsl_sess_alloc with "Hctx HkA Hunreg HkB HkB' HtA").
Qed.

Lemma nsl_sess_alloc_resp lvl kA kB tA tB E :
  ↑cryptoN.@"nsl" ⊆ E →
  nsl_ctx -∗
  nsl_key Resp kB -∗
  unregistered tB -∗
  pub_enc_key kA -∗
  guarded lvl (nsl_key Init kA) -∗
  stermT lvl tB -∗
  stermT lvl tA ={E}=∗
  guarded lvl (term_session_auth tB (Session Resp kA kB (Some tA)) ∗
               term_session_frag tB (Session Resp kA kB (Some tA))).
Proof.
iIntros (?) "#Hctx #HkB Hunreg #HkA #HkA' #HtB #HtA".
by iApply (nsl_sess_alloc with "Hctx HkB Hunreg HkA HkA' HtB")=> /=; eauto.
Qed.

Lemma session_map_auth_included t s SM :
  {[t := session_auth s]} ≼ to_session_map SM ↔
  SM !! t = Some s.
Proof.
split.
- move=> e; apply/leibniz_equiv.
  case/singleton_included_l: e=> x [].
  rewrite lookup_fmap option_equivE.
  case: (SM !! t)=> [s'|] //= <-.
  rewrite Some_included; case.
  + by case=> /= _; rewrite option_equivE.
  + by rewrite session_auth_included=> <-.
- move=> e; apply/singleton_included_l.
  exists (session_auth_frag s).
  by rewrite lookup_fmap e /= Some_included session_auth_included; eauto.
Qed.

Lemma session_map_frag_included t s SM :
  {[t := session_frag s]} ≼ to_session_map SM ↔
  ∃ s', SM !! t = Some s' ∧ to_session s ≼ to_session s'.
Proof.
split.
- case/singleton_included_l=> x [].
  rewrite lookup_fmap option_equivE.
  case: (SM !! t)=> [s'|] //= <-.
  rewrite Some_included; case.
  + by case=> /=; rewrite option_equivE.
  + rewrite session_frag_included; eauto.
- case=> s' [H1 H2].
  apply/singleton_included_l.
  rewrite lookup_fmap H1 /=.
  exists (session_auth_frag s'); split=> //.
  by rewrite Some_included session_frag_included; right.
Qed.

Lemma term_session_nsl_key E lvl t s :
  ↑cryptoN.@"nsl" ⊆ E →
  nsl_ctx -∗
  guarded lvl (term_session_frag t s) ={E}=∗
  ▷ guarded lvl (nsl_key s.(srole) (sowner s)).
Proof.
move=> sub; iIntros "#Hctx Hterm"; case: lvl => //=.
iMod (auth_acc to_session_map _ _ _ _ {[t := session_frag s]}
         with "[Hctx Hterm]") as "Hinv"; try by eauto.
iDestruct "Hinv" as (SM) "(%Hincl & Hinv & Hclose)".
iAssert (▷ nsl_key s.(srole) (sowner s))%I with "[Hinv]" as "#Hs".
  case/session_map_frag_included: Hincl=> s' [SM_t ss'].
  iModIntro.
  rewrite /sowner; case/to_session_included: ss'=> -> [-> [-> _]].
  by iDestruct ("Hinv" $! _ _ SM_t) as "(?&?&?&?&?&?)".
by iMod ("Hclose" $! SM {[t := session_frag s]} with "[Hinv]"); eauto.
Qed.

Definition session_inv' t1 s1 : iProp Σ :=
  nsl_key s1.(srole) (sowner s1)
  ∗ nsl_key (sroleo s1) (sother s1)
  ∗ registered t1
  ∗ stermT Sec t1
  ∗ (if sdata s1 is Some t2 then stermT Sec t2 else True).

Lemma term_session_session_inv0 E lvl t s :
  ↑cryptoN.@"nsl" ⊆ E →
  nsl_ctx -∗
  guarded lvl (term_session_frag t s) ={E}=∗
  ∃ s', ⌜to_session s ≼ to_session s'⌝ ∗ ▷ guarded lvl (session_inv' t s').
Proof.
move=> sub; iIntros "#Hctx Hterm"; case: lvl => //=.
  by iExists s.
iMod (auth_acc to_session_map _ _ _ _ {[t := session_frag s]}
         with "[Hctx Hterm]") as "Hinv"; try by eauto.
iDestruct "Hinv" as (SM) "(%Hincl & #Hinv & Hclose)".
case/session_map_frag_included: Hincl=> s' [SM_t ss'].
iExists s'.
iAssert (▷ session_inv' t s')%I with "[Hinv]" as "#Hs".
  iModIntro.
  iDestruct ("Hinv" $! _ _ SM_t) as "(?&?&?&?&?&?)".
  by iSplit => //; eauto.
by iMod ("Hclose" $! SM {[t := session_frag s]} with "[Hinv]"); eauto.
Qed.

Lemma term_session_session_inv1 E lvl rl kA kB t t' :
  ↑cryptoN.@"nsl" ⊆ E →
  let s := Session rl kA kB (Some t') in
  nsl_ctx -∗
  guarded lvl (term_session_frag t s) ={E}=∗
  ▷ guarded lvl (session_inv' t s).
Proof.
move=> sub s; iIntros "#Hctx #Hterm".
iMod (term_session_session_inv0 with "Hctx Hterm") as (s') "[%s_s' Hs']" => //.
do 2!iModIntro.
rewrite /session_inv' /sowner /sother /sroleo /=.
by case/to_session_included: s_s' => <- [] <- [] <- <- /=.
Qed.

Lemma term_session_session_inv2 E lvl t s :
  ↑cryptoN.@"nsl" ⊆ E →
  nsl_ctx -∗
  termT lvl t -∗
  guarded lvl (term_session_frag t s) ={E}=∗
  ▷ stermT lvl t.
Proof.
iIntros (sub) "#Hctx #Ht #Hsess".
iMod (term_session_session_inv0 with "Hctx Hsess") as (s') "[%s_s' Hs']" => //.
iDestruct "Hs'" as "(_&_&_&#Ht'&_)".
by case: lvl=> //=; do 2!iModIntro; iSplit; eauto.
Qed.

Lemma term_session_session_inv3 E lvl t s :
  ↑cryptoN.@"nsl" ⊆ E →
  nsl_ctx -∗
  termT lvl (TKey KAEnc (sowner s)) -∗
  guarded lvl (term_session_frag t s) ={E}=∗
  ▷ pub_enc_key (sowner s).
Proof.
iIntros (sub) "#Hctx #Ht #Hsess".
iMod (term_session_session_inv0 with "Hctx Hsess") as (s') "[%s_s' Hs']" => //.
iDestruct "Hs'" as "(#Hk&_)".
case: lvl=> //=; do 2!iModIntro.
  by iApply termT_TAEncE.
rewrite /sowner.
case/to_session_included: s_s' => [] <- [] <- [] <- _.
by iDestruct "Hk" as "[??]"; iExists _, _; eauto.
Qed.

Lemma term_session_session_inv4 E lvl t s :
  ↑cryptoN.@"nsl" ⊆ E →
  nsl_ctx -∗
  guarded lvl (term_session_frag t s) ={E}=∗
  ▷ guarded lvl (nsl_key (srole s) (sowner s)).
Proof.
iIntros (sub) "#Hctx #Hsess".
iMod (term_session_session_inv0 with "Hctx Hsess") as (s') "[%s_s' Hs']" => //.
iDestruct "Hs'" as "(#Hk&_)".
case: lvl=> //=; do 2!iModIntro.
rewrite /sowner.
by case/to_session_included: s_s' => [] <- [] <- [] <- _.
Qed.

Arguments sroleo !_ /.
Arguments sother !_ /.
Arguments sowner !_ /.

Lemma nsl_sess_update lvl kA kB tA tB E :
  ↑cryptoN.@"nsl" ⊆ E →
  nsl_ctx -∗
  guarded lvl (term_session_auth tA (Session Init kA kB None)) -∗
  guarded lvl (term_session_frag tB (Session Resp kA kB (Some tA))) ={E}=∗
  guarded lvl (term_session_auth tA (Session Init kA kB (Some tB)) ∗
               term_session_frag tA (Session Init kA kB (Some tB))).
Proof.
iIntros (sub) "Hctx HA HB"; case: lvl => //=.
case: (decide (tA = tB))=> [<-|tAB].
  iPoseProof (term_session_agree with "HA HB") as "%agree".
  by rewrite to_session_included /= in agree *; intuition.
set s1 := Session Init _ _ _; set s2 := Session Resp _ _ _.
pose (f1 := {[tA := session_auth s1]} : gmap _ _).
pose (f2 := {[tB := session_frag s2]} : gmap _ _).
iMod (auth_acc to_session_map _ _ _ _
         (f1 ⋅ f2) with "[Hctx HA HB]") as "Hinv"; try by eauto.
  by rewrite auth_own_op; iFrame.
iDestruct "Hinv" as (SM) "(%Hincl & #Hinv & Hclose)".
have /session_map_auth_included SM_tA : f1 ≼ to_session_map SM.
  apply: cmra_included_trans Hincl; exact: cmra_included_l.
have /session_map_frag_included SM_tB: f2 ≼ to_session_map SM.
  apply: cmra_included_trans Hincl; exact: cmra_included_r.
case: SM_tB=> s2' [SM_tB s2_incl].
move: SM_tB; rewrite -(to_session_included_eq s2_incl) /=; last by eauto.
move=> SM_tB {s2' s2_incl}.
set s1' := Session Init kA kB (Some tB).
pose (f1' := {[tA := session_auth_frag s1']} : gmap _ _).
pose (SM' := <[tA := s1']> SM).
iMod ("Hclose" $! (<[tA := s1']>SM) (f1' ⋅ f2) with "[]") as "Hown"; last first.
  rewrite /f1' -singleton_op !auth_own_op; iModIntro.
  by iDestruct "Hown" as "[[??]?]"; iFrame.
have f2_tA : f2 !! tA = None by rewrite lookup_singleton_ne.
iSplit.
  iPureIntro.
  rewrite /to_session_map fmap_insert -![_ ⋅ f2]insert_singleton_op //.
  rewrite -(insert_insert f2 tA (session_auth_frag s1') (session_auth s1)).
  eapply insert_local_update.
  - by rewrite lookup_fmap SM_tA.
  - by rewrite lookup_insert.
  apply local_update_unital_discrete.
  intros a _ <-%cancelable=> //; last by apply _.
  split=> //; first exact: session_auth_frag_valid.
  rewrite {2}/session_auth_frag -cmra_assoc -auth_frag_op -Some_op.
  by rewrite /to_session /= -!pair_op !agree_idemp.
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

Variable send recv gen : val.

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None).

Definition initiator (skA pkA pkB nA : val) : val := λ: <>,
  bind: "m1"   := enc pkB (tag "m1" (term_of_list [nA; pkA])) in
  send "m1";;
  bind: "m2"   := dec skA (recv #()) in
  bind: "m2"   := untag "m2" "m2" in
  bind: "m2"   := list_of_term "m2" in
  bind: "nA'"  := "m2" !! #0 in
  bind: "nB"   := "m2" !! #1 in
  bind: "pkB'" := "m2" !! #2 in
  if: eq_term "nA'" nA && eq_term "pkB'" pkB then
    bind: "m3" := enc pkB (tag "m3" "nB") in
    send "m3";;
    SOME "nB"
  else NONE.

Definition responder (skB pkB : val) : val := λ: <>,
  bind: "m1" := dec skB (recv #()) in
  bind: "m1" := untag "m1" "m1" in
  bind: "m1" := list_of_term "m1" in
  bind: "nA" := "m1" !! #0 in
  bind: "pkA" := "m1" !! #1 in
  bind: "kt" := is_key "pkA" in
  if: "kt" = repr KAEnc then
    let: "nB" := gen #() in
    let: "m2" := tag "m2" (term_of_list ["nA"; "nB"; pkB]) in
    bind: "m2" := enc "pkA" "m2" in
    send "m2";;
    bind: "m3" := dec skB (recv #()) in
    bind: "nB'" := untag "m3" "m3" in
    if: eq_term "nB'" "nB" then SOME ("pkA", "nA", "nB") else NONE
  else NONE.

Implicit Types Ψ : val → iProp Σ.

Hypothesis wp_send : forall E t Ψ,
  ▷ termT Pub t -∗
  Ψ #() -∗
  WP send t @ E {{ Ψ }}.

Hypothesis wp_recv : forall E Ψ,
  (∀ t, termT Pub t -∗ Ψ t) -∗
  WP recv #() @ E {{ Ψ }}.

Hypothesis wp_gen : forall E lvl Ψ,
  (∀ t, unregistered t -∗ stermT lvl t -∗
        Ψ t) -∗
  WP gen #() @ E {{ Ψ }}.

Lemma termT_msg1 lvl kA kB (tA : term) :
  nsl_key Init kA -∗
  stermT lvl tA -∗
  pub_enc_key kB -∗
  guarded lvl (nsl_key Resp kB) -∗
  guarded lvl (term_session_frag tA (Session Init kA kB None)) -∗
  termT Pub (TEnc true kB (Spec.tag "m1" (Spec.of_list [tA; TKey KAEnc kA]))).
Proof.
iIntros "#HkA #HtA #HkB_lo (#HkB_hi & #HkB_m1 & _) #frag".
iApply termT_aenc_pub_secG; eauto.
  iApply termT_tag; iApply termT_of_list => /=.
  iSplit; first by iDestruct "HtA" as "[??]".
  iSplit => //.
  iApply (@sub_termT _ _ _ Pub) => //.
  by iDestruct "HkA" as "[HkA _]"; iApply termT_TAEnc.
case: lvl => //=; iModIntro.
iApply (tagged_inv_intro with "HkB_m1"); iModIntro => /=.
by iExists _, _; eauto.
Qed.

(* MOVE *)
Global Instance guarded_into_and b lvl (P Q R : iProp Σ) :
  IntoAnd b P Q R →
  IntoAnd b (guarded lvl P) (guarded lvl Q) (guarded lvl R).
Proof.
by case: b lvl=> [] //= [] //= _; rewrite /IntoAnd /=; eauto.
Qed.

Lemma stermTP lvl lvl' t :
  stermT lvl t -∗ termT lvl' t -∗ ⌜lvl ⊑ lvl'⌝.
Proof. by iIntros "[_ #min]". Qed.

Lemma stermT_eq lvl lvl' t :
  stermT lvl t -∗ stermT lvl' t -∗ ⌜lvl = lvl'⌝.
Proof.
iIntros "[#Ht #min] [#Ht' #min']".
iPoseProof ("min" with "Ht'") as "%l1".
iPoseProof ("min'" with "Ht") as "%l2".
by case: lvl lvl' l1 l2 => [] // [] //.
Qed.
(* /MOVE *)

Lemma wp_initiator kA kB (tA : term) lvl E Ψ :
  ↑cryptoN.@"nsl" ⊆ E →
  nsl_ctx -∗
  stermT lvl tA -∗
  unregistered tA -∗
  nsl_key Init kA -∗
  pub_enc_key kB -∗
  guarded lvl (nsl_key Resp kB) -∗
  (∀ onB : option term,
      (if onB is Some tB then
         stermT lvl tB ∗
         guarded lvl (
           term_session_auth tA (Session Init kA kB (Some tB)) ∗
           term_session_frag tB (Session Resp kA kB (Some tA))
         )
       else True) -∗
      Ψ (repr onB)) -∗
  WP initiator (TKey KADec kA) (TKey KAEnc kA) (TKey KAEnc kB) tA #() @ E
     {{ Ψ }}.
Proof.
rewrite /initiator.
iIntros (?) "#Hctx #HtA unreg #HkA #HkB_lo #HkB_hi Hpost".
wp_list (_ :: _ :: []).
wp_term_of_list.
wp_tag.
wp_enc.
iMod (nsl_sess_alloc_init lvl kA kB
        with "Hctx HkA unreg HkB_lo HkB_hi HtA") as "[auth #fragA]"=> //.
wp_pures; wp_bind (send _); iApply wp_send.
  by iModIntro; iApply termT_msg1.
wp_pures; wp_bind (recv _); iApply wp_recv.
iIntros (m2) "#Hm2"; wp_dec m2; last protocol_failure.
wp_untag m2; last protocol_failure.
wp_list_of_term m2; last protocol_failure.
wp_lookup nA' enA'; last protocol_failure.
wp_lookup nB  enB; last protocol_failure.
wp_lookup pkB' epkB'; last protocol_failure.
wp_eq_term e; last protocol_failure; subst nA'.
wp_eq_term e; last protocol_failure; subst pkB'.
wp_tag.
wp_enc.
iPoseProof "HkA" as "[??]".
iDestruct (termT_adec_pub_sec with "Hm2 [//]") as (lm2) "{Hm2} [#Hm2 #fragB]".
iPoseProof (termT_untag with "Hm2") as "{Hm2} Hm2".
iPoseProof (termT_of_listE with "Hm2") as "{Hm2} Hm2".
iPoseProof (big_sepL_lookup with "Hm2") as "m2_tA"; first exact: enA'.
iPoseProof (big_sepL_lookup with "Hm2") as "m2_nB"; first exact: enB.
iPoseProof (big_sepL_lookup with "Hm2") as "m2_kB"; first exact: epkB'.
set  sA := Session Init kA kB _.
pose sB := Session Resp kA kB (Some tA).
pose sA' := Session Init kA kB (Some nB).
iAssert (guarded lm2 (term_session_frag nB sB)) as "{fragB} #fragB".
  case: lm2 => //=.
  iDestruct (tagged_inv_elim' with "[//] fragB") as "{fragB} #fragB".
  iDestruct "fragB" as (nA' nB' kB') "/= (%em2 & fragB)".
  move/Spec.of_list_inj in em2; subst m2.
  by case: enA' epkB' enB => [] -> [] -> [] -> {nA' nB' kB'}.
iClear (enA' enB epkB') "Hm2".
iPoseProof (stermTP with "HtA m2_tA") as "{m2_tA} %Hlm2".
iMod (term_session_session_inv1 with "Hctx fragB") as "#sessB" => //.
iAssert (▷ ⌜lm2 = lvl⌝)%I as "e".
  iModIntro.
  case: lvl lm2 Hlm2 => [] // [] //= _.
  iDestruct "sessB" as "(_&_&_&_&HtA')".
  by iApply (stermT_eq with "HtA' HtA").
wp_pures; iDestruct "e" as "->".
iMod (nsl_sess_update with "Hctx auth fragB") as "{fragA} [auth #fragA]" => //.
set m3 := TEnc _ _ _.
wp_bind (send _); iApply wp_send.
  iModIntro.
  iDestruct "HkB_hi" as "(HkB_hi & _ & HhB_m3)".
  iApply (termT_aenc_pub_secG _ _ lvl) => //; eauto.
    by iApply termT_tag.
  case: (lvl) => //=; iModIntro.
  iApply tagged_inv_intro; eauto.
  by iModIntro; iExists tA, kA; iSplit.
wp_pures; iApply ("Hpost" $! (Some nB)).
case: lvl {Hlm2} => /=.
  do 2![iSplit => //]; by iModIntro; iIntros (lvl') "?".
iFrame; iSplit; by iDestruct "sessB" as "(?&?&?&?&?&?)".
Qed.

Lemma stermT_termT lvl t : stermT lvl t -∗ termT lvl t.
Proof. by iDestruct 1 as "[??]". Qed.

Lemma sub_termT_pub lvl t : termT Pub t -∗ termT lvl t.
Proof. by iApply sub_termT. Qed.

Lemma wp_responder kB E Ψ :
  ↑cryptoN.@"nsl" ⊆ E →
  nsl_ctx -∗
  nsl_key Resp kB -∗
  (∀ ot : option (term * term * term),
      (if ot is Some (pkA, nA, nB) then
         ∃ lvl kA,
           ⌜pkA = TKey KAEnc kA⌝ ∗
           pub_enc_key kA ∗
           stermT lvl nA ∗
           stermT lvl nB ∗
           guarded lvl (
            term_session_frag nA (Session Init kA kB (Some nB)) ∗
            term_session_auth nB (Session Resp kA kB (Some nA)))
       else True) -∗
       Ψ (repr ot)) -∗
  WP responder (TKey KADec kB) (TKey KAEnc kB) #() @ E {{ Ψ }}.
Proof.
iIntros (?) "#Hctx #HkB Hpost".
rewrite /responder; wp_pures.
wp_bind (recv _); iApply wp_recv; iIntros (m1) "#Hm1".
wp_dec m1; last protocol_failure.
wp_untag m1; last protocol_failure.
wp_list_of_term m1; last protocol_failure.
wp_lookup nA enA; last protocol_failure.
wp_lookup pkA epkA; last protocol_failure.
wp_is_key_eq kt kA et; last protocol_failure; subst pkA.
wp_pures.
case: (bool_decide_reflect (_ = repr_key_type KAEnc)); last protocol_failure.
case: kt epkA=> // epkA _.
iPoseProof "HkB" as "(?& HkB_m1 & HkB_m3)".
iDestruct (termT_adec_pub_sec with "Hm1 [//]") as (lm1) "{Hm1} [Hm1 fragA]".
iPoseProof (termT_untag with "Hm1") as "{Hm1} Hm1".
iPoseProof (termT_of_listE with "Hm1") as "{Hm1} Hm1".
iPoseProof (big_sepL_lookup with "Hm1") as "HnA"; first exact: enA.
iPoseProof (big_sepL_lookup with "Hm1") as "HpkA"; first exact: epkA.
pose Pm1 := term_session_frag nA (Session Init kA kB None).
iAssert (guarded lm1 Pm1) as "{fragA} fragA".
  iApply (guarded_mono with "fragA").
  iIntros "!> {fragA} #fragA".
  iPoseProof (tagged_inv_elim' with "HkB_m1 fragA") as "{fragA} fragA".
  iDestruct "fragA" as (nA' kA') "/= [%em1 #fragA]".
  move/Spec.of_list_inj in em1; subst m1.
  by case: enA epkA => [] -> [] -> {nA' kA'}.
iMod (term_session_session_inv2 with "Hctx HnA fragA") as "{HnA} #HnA" => //.
iMod (@term_session_session_inv3 _ _ _ (Session Init kA _ _) with "Hctx HpkA fragA") as "#HkA_lo" => //=.
iMod (term_session_session_inv4 with "Hctx fragA") as "#HkA_hi" => //.
wp_pures; wp_bind (gen _); iApply (wp_gen _ lm1); iIntros (nB) "unreg #HnB".
wp_pures.
wp_list (_ :: _ :: _ :: []); wp_term_of_list. 
wp_tag; wp_enc; wp_pures.
set m2 := Spec.of_list [nA; nB; TKey KAEnc kB].
set sB := Session Resp kA kB (Some nA).
iMod (nsl_sess_alloc_resp _ kA kB nA with "Hctx HkB unreg HkA_lo HkA_hi HnB HnA")
    as "[auth #fragB]"=> //=.
wp_bind (send _); iApply wp_send.
  iModIntro.
  iDestruct "HkA_hi" as "(HkA_hi & HkA_m2)".
  iApply termT_aenc_pub_secG; eauto.
    iApply termT_tag; iApply termT_of_list => /=.
    do !iSplit => //; try by iApply stermT_termT.
    by iApply sub_termT_pub; iApply termT_TAEnc.
  case: lm1 => //=; iModIntro.
  iApply tagged_inv_intro; eauto.
  by iModIntro; iExists nA, nB, kB; iSplit; first trivial.
wp_pures; wp_bind (recv _); iApply wp_recv; iIntros (m3) "#Hm3".
wp_dec m3; last protocol_failure.
iPoseProof "HkB" as "[? _]".
iDestruct (termT_adec_pub_sec with "Hm3 [//]") as (lm3) "/= {Hm3} [#Hm3 #Hprot3]".
wp_untag m3; last protocol_failure.
wp_eq_term e; last protocol_failure; subst m3.
iPoseProof (termT_untag with "Hm3") as "{Hm3} Hm3".
iAssert (⌜lm1 ⊑ lm3⌝)%I as "%lm1_lm3".
  by iDestruct "HnB" as "[_ #Hmin]"; iApply "Hmin".
iPoseProof (guarded_leq with "Hprot3") as "{Hprot3 Hm3} Hprot3"; first eassumption.
clear lm1_lm3 lm3.
wp_pures.
iApply ("Hpost" $! (Some (_, _, _))).
iExists _, _; do 4![iSplit => //].
case: lm1 => //=.
iDestruct (tagged_inv_elim' with "HkB_m3 Hprot3") as (nA' kA') "[#frag1 #frag2]".
set sB' := (Session Resp kA' _ _).
iPoseProof (term_session_agree with "auth frag2") as "%sess".
have [-> ->] : sB' = sB by apply: to_session_included_eq => //=; eauto.
by iSplit=> //.
Qed.

End NSL.
