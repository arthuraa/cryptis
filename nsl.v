From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl namespace_map frac.
From iris.base_logic.lib Require Import auth.
From iris.heap_lang Require Import notation proofmode.
From crypto Require Import lib term crypto1 primitives.

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
}.

Context `{!nslG}.

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

Definition initiator_pred kA t : iProp Σ :=
  match t with
  | TPair nA (TPair nB (TPair (TKey KAEnc kB) _)) =>
    term_session_frag nB (Session Resp kA kB (Some nA))
  | _ => False
  end.

Global Instance initiator_pred_proper : NonExpansive2 initiator_pred.
Proof. solve_contractive. Qed.

Definition responder_pred kB t : iProp Σ :=
  match t with
  | TPair nA (TKey KAEnc kA) => term_session_frag nA (Session Init kA kB None)
  | _ => False
  end
  ∨ ∃ kA nA, term_session_frag nA (Session Init kA kB (Some t)).

Global Instance responder_pred_proper : NonExpansive2 responder_pred.
Proof. solve_contractive. Qed.

Global Instance initiator_pred_persistent lA t :
  Persistent (initiator_pred lA t).
Proof.
case: t; try by move=> *; apply _.
move=> nA; case; try by move=> *; apply _.
move=> nB; case; try by move=> *; apply _.
case; try by move=> *; apply _.
by case; move=> *; apply _.
Qed.

Global Instance responder_pred_persistent lB t :
  Persistent (responder_pred lB t).
Proof.
case: t; try by move=> *; apply _.
move=> nA; case; try by move=> *; apply _.
case; try by move=> *; apply _.
Qed.

Definition agent_pred rl l :=
  match rl with
  | Init => OfeMor (initiator_pred l)
  | Resp => OfeMor (responder_pred l)
  end.

Global Instance agent_pred_persistent rl l t :
  Persistent (agent_pred rl l t).
Proof. by case: rl; apply _. Qed.

Definition unregistered l : iProp Σ :=
  meta_token l (↑cryptoN.@"nsl".@"secret").

Definition registered t l : iProp Σ :=
  ⌜symbols_of_term t = {[l]}⌝
  ∗ meta l (cryptoN.@"nsl".@"secret") ().

Lemma registered_unregistered t l :
  registered t l -∗
  unregistered l -∗
  False.
Proof.
iIntros "[#Hl #Hmeta] Hunreg".
by iApply (meta_contra with "Hunreg Hmeta").
Qed.

Global Instance registered_persistent t l :
  Persistent (registered t l).
Proof. apply _. Qed.

Global Instance registered_timeless t l :
  Timeless (registered t l).
Proof. apply _. Qed.

Definition nsl_key rl k : iProp Σ :=
  meta k (cryptoN.@"nsl") rl
  ∗ akeyT Pub Sec (agent_pred rl k) k.

Global Instance nsl_key_persistent rl k :
  Persistent (nsl_key rl k).
Proof. apply _. Qed.

Definition coherent_views SM t1 s1 : Prop :=
  match s1.(srole), s1.(sdata) with
  | Init, None => True
  | Init, Some t2 =>
    SM !! t2 = Some (Session Resp s1.(sinit) s1.(sresp) (Some t1))
  | Resp, None => False
  | Resp, Some _ => True
  end.

Definition session_inv SM : iProp Σ :=
  ∀ t1 s1, ⌜SM !! t1 = Some s1⌝ -∗ ∃ l1,
    registered t1 l1
    ∗ stermT Sec t1
    ∗ (if s1.(sdata) is Some t2 then stermT Sec t2 else True)
    ∗ nsl_key s1.(srole) (sowner s1)
    ∗ ⌜coherent_views SM t1 s1⌝.

Definition nsl_inv : iProp Σ :=
  auth_inv nsl_sess_name to_session_map session_inv.

Definition nsl_ctx : iProp Σ :=
  auth_ctx nsl_sess_name (cryptoN.@"nsl") to_session_map session_inv.

Lemma nsl_sess_alloc kA kB t rl l E ot :
  ↑cryptoN.@"nsl" ⊆ E →
  symbols_of_term t = {[l]} →
  (if rl is Init then ot = None else is_Some ot) →
  nsl_ctx -∗
  nsl_key rl (if rl is Init then kA else kB) -∗
  unregistered l -∗
  stermT Sec t -∗
  (if ot is Some t' then stermT Sec t' else True) ={E}=∗
  term_session_auth t (Session rl kA kB ot) ∗
  term_session_frag t (Session rl kA kB ot).
Proof.
move=> sub t_l rl_ot; iIntros "#Hctx #Howner Hl #Ht #Ht'".
iMod (auth_empty nsl_sess_name) as "#Hinit".
(* FIXME Why do I have to provide this instance? *)
iMod (auth_acc to_session_map _ _ _ _ ε
         with "[Hctx Hinit]") as "Hinv"; try by eauto.
iDestruct "Hinv" as (SM) "(_ & Hinv & Hclose)".
iAssert (▷ ⌜∀ t', symbols_of_term t' = {[l]} → SM !! t' = None⌝)%I
        as "# > %Hfresh".
  iIntros (t') "%t'_l".
  destruct (SM !! t') as [s_t|] eqn:SM_t=> //.
  iDestruct ("Hinv" $! _ _ SM_t) as (l') "(>Hreg&_&_&?)".
  iDestruct "Hreg" as "[%t'_l' Hreg]".
  have -> : l' = l by apply/elem_of_singleton; set_solver.
  by iDestruct (meta_contra with "Hl Hreg") as "[]".
set s := Session rl kA kB ot.
iMod (meta_set _ _ () with "Hl") as "#Hmeta"; eauto.
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
  iExists l; iSplit; first by iSplit.
  iSplit=> //.
  rewrite /s; do 2![iSplit=> //]; case: (rl) rl_ot=> // rl_ot.
    by rewrite rl_ot.
  by case: rl_ot=> t' -> /=.
rewrite lookup_insert_ne //; iIntros (SM_t1').
iDestruct ("Hinv" $! _ _ SM_t1')
  as (l1) "(Hreg & Ht1' & Ht2' & Howner' & %Hcoh)".
iExists l1; iFrame; iPureIntro.
move: Hcoh; rewrite /coherent_views.
case: (srole s1') (sdata s1')=> [|] [t2'|] //.
case: (decide (t = t2'))=> [<-|?]; first by rewrite Hfresh.
by rewrite lookup_insert_ne.
Qed.

Lemma nsl_sess_alloc_init kA kB tA l E :
  ↑cryptoN.@"nsl" ⊆ E →
  symbols_of_term tA = {[l]} →
  nsl_ctx -∗
  nsl_key Init kA -∗
  unregistered l -∗
  stermT Sec tA ={E}=∗
  term_session_auth tA (Session Init kA kB None) ∗
  term_session_frag tA (Session Init kA kB None).
Proof.
iIntros (??) "#Hctx #HkA Hunreg #HtA".
by iApply (nsl_sess_alloc with "Hctx HkA Hunreg HtA").
Qed.

Lemma nsl_sess_alloc_resp kA kB tA tB l E :
  ↑cryptoN.@"nsl" ⊆ E →
  symbols_of_term tB = {[l]} →
  nsl_ctx -∗
  nsl_key Resp kB -∗
  unregistered l -∗
  stermT Sec tB -∗
  stermT Sec tA ={E}=∗
  term_session_auth tB (Session Resp kA kB (Some tA)) ∗
  term_session_frag tB (Session Resp kA kB (Some tA)).
Proof.
iIntros (??) "#Hctx #HkA Hunreg #HtB #HtA".
by iApply (nsl_sess_alloc with "Hctx HkA Hunreg HtB")=> /=; eauto.
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

Lemma term_session_auth_termT E t s :
  ↑cryptoN.@"nsl" ⊆ E →
  nsl_ctx -∗
  term_session_frag t s ={E}=∗
  ▷ (stermT Sec t
     ∗ if s.(sdata) is Some t' then stermT Sec t' else True).
Proof.
move=> sub.
iIntros "#Hctx Hterm".
iMod (auth_acc to_session_map _ _ _ _ {[t := session_frag s]}
         with "[Hctx Hterm]") as "Hinv"; try by eauto.
iDestruct "Hinv" as (SM) "(%Hincl & Hinv & Hclose)".
iAssert (▷ (stermT Sec t ∗
            if s.(sdata) is Some t' then stermT Sec t'
            else True))%I with "[Hinv]" as "#Ht".
  case/session_map_frag_included: Hincl=> s' [SM_t ss'].
  iModIntro.
  iDestruct ("Hinv" $! _ _ SM_t) as (l) "(?&?&?&?&?)"; iFrame.
  case/to_session_included: ss'=> _ [_ [_]].
  by case: (sdata s)=> [? [<-]|].
by iMod ("Hclose" $! SM {[t := session_frag s]} with "[Hinv]"); eauto.
Qed.

Lemma term_session_nsl_key E t s :
  ↑cryptoN.@"nsl" ⊆ E →
  nsl_ctx -∗
  term_session_frag t s ={E}=∗
  ▷ nsl_key s.(srole) (sowner s).
Proof.
move=> sub.
iIntros "#Hctx Hterm".
iMod (auth_acc to_session_map _ _ _ _ {[t := session_frag s]}
         with "[Hctx Hterm]") as "Hinv"; try by eauto.
iDestruct "Hinv" as (SM) "(%Hincl & Hinv & Hclose)".
iAssert (▷ nsl_key s.(srole) (sowner s))%I with "[Hinv]" as "#Hs".
  case/session_map_frag_included: Hincl=> s' [SM_t ss'].
  iModIntro.
  rewrite /sowner; case/to_session_included: ss'=> -> [-> [-> _]].
  by iDestruct ("Hinv" $! _ _ SM_t) as (l) "(?&?&?&?&?)".
by iMod ("Hclose" $! SM {[t := session_frag s]} with "[Hinv]"); eauto.
Qed.

Lemma nsl_sess_update kA kB tA tB E :
  ↑cryptoN.@"nsl" ⊆ E →
  nsl_ctx -∗
  term_session_auth tA (Session Init kA kB None) -∗
  term_session_frag tB (Session Resp kA kB (Some tA)) ={E}=∗
  term_session_auth tA (Session Init kA kB (Some tB)) ∗
  term_session_frag tA (Session Init kA kB (Some tB)).
Proof.
iIntros (sub) "Hctx HA HB".
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
  iDestruct ("Hinv" $! _ _ SM_tA) as (l1) "(Hreg & Ht & _ & Howner & %Hcoh)".
  iDestruct ("Hinv" $! _ _ SM_tB) as (l2) "(_ & Ht' & _ & _ & _)".
  iExists l1; do 4![iSplit=> //]; iPureIntro.
  rewrite /coherent_views /= lookup_insert_ne // SM_tB.
  rewrite to_session_included /= in s2_incl *.
  by destruct 1 as (-> & -> & -> & ->); case: (s2').
rewrite lookup_insert_ne //.
iIntros "%SM_t"; iDestruct ("Hinv" $! _ _ SM_t) as (l) "(?&?&?&?&%Hcoh)".
iExists l; do 4![iSplit=> //]; iPureIntro.
move: Hcoh; rewrite /coherent_views.
case erole: (srole s)=> //.
case edata: (sdata s)=> [t'|] //.
case: (decide (tA = t'))=> [<-|?]; first by rewrite SM_tA.
by rewrite lookup_insert_ne.
Qed.

Variable send recv gen : val.

Definition initiator (skA pkA pkB nA : val) : val := λ: <>,
  bind: "m1"   := enc pkB (tuple nA pkA) in
  send "m1";;
  bind: "m2"   := dec skA (recv #()) in
  bind: "nA'"  := term_proj "m2" #0 in
  bind: "nB"   := term_proj "m2" #1 in
  bind: "pkB'" := term_proj "m2" #2 in
  if: eq_term "nA'" nA && eq_term "pkB'" pkB then
    bind: "m3" := enc pkB "nB" in
    send "m3";;
    SOME "nB"
  else NONE.

Definition responder (skB pkB : val) : val := λ: <>,
  bind: "m1"  := dec skB (recv #()) in
  bind: "nA" := term_proj "m1" #0 in
  bind: "pkA" := term_proj "m1" #1 in
  let: "nB" := gen #() in
  bind: "m2" := enc "pkA" (tuple "nA" (tuple "nB" (tuple pkB (TInt 0)))) in
  send "m2";;
  bind: "nB'" := dec skB (recv #()) in
  if: "nB'" = "nB" then SOME ("pkA", "nA", "nB") else NONE.

Implicit Types Ψ : val → iProp Σ.

Hypothesis wp_send : forall E t Ψ,
  ▷ termT Pub t -∗
  Ψ #() -∗
  WP send t @ E {{ Ψ }}.

Hypothesis wp_recv : forall E Ψ,
  (∀ t, termT Pub t -∗ Ψ t) -∗
  WP recv #() @ E {{ Ψ }}.

Hypothesis wp_gen : forall E lvl Ψ,
  (∀ t l, ⌜symbols_of_term t = {[l]}⌝ -∗
          stermT lvl t -∗
          unregistered l -∗
          Ψ t) -∗
  WP gen #() @ E {{ Ψ }}.

Ltac protocol_failure :=
  by move=> *; wp_pures; iExists None.

Lemma wp_initiator_honest kA kB (tA : term) l E :
  ↑cryptoN.@"nsl" ⊆ E →
  symbols_of_term tA = {[l]} →
  nsl_ctx -∗
  stermT Sec tA -∗
  unregistered l -∗
  nsl_key Init kA -∗
  nsl_key Resp kB -∗
  WP initiator (TKey KADec kA) (TKey KAEnc kA) (TKey KAEnc kB) tA #() @ E
     {{v, ∃ onB : option term,
          ⌜v = repr onB⌝ ∗
          match onB with
          | Some tB => term_session_auth tA (Session Init kA kB (Some tB))
          | None => True
          end}}.
Proof.
rewrite /initiator.
iIntros (? Hfresh) "#Hctx #HtA Hown #HkA #HkB".
wp_pures; wp_bind (tuple _ _); iApply wp_tuple.
iMod (nsl_sess_alloc_init kA kB with "Hctx HkA Hown HtA") as "[tok #?]"=> //.
wp_bind (enc _ _); iApply wp_enc; wp_pures.
wp_bind (send _); iApply wp_send.
  rewrite /=; iExists Pub, Sec, _=> /=.
  iDestruct "HkB" as "[??]".
  iSplit; eauto.
  iLeft; iSplit; rewrite /=; first by iModIntro; iLeft.
  iSplit.
    by iDestruct "HtA" as "[??]".
  iExists Pub, (agent_pred Init kA); iSplit; last by iPureIntro.
  iExists Sec; by iDestruct "HkA" as "[??]".
wp_pures; wp_bind (recv _); iApply wp_recv.
iIntros (m2) "#Hm2".
wp_bind (dec _ _); iApply wp_dec.
case: m2; try by protocol_failure.
case; last by protocol_failure.
move=> k t; rewrite /=.
case: decide=> [ {k}<-|ne]; last by wp_pures; iExists None.
iDestruct "Hm2" as (lvl_enc lvl_dec Φ) "[HkA1 Ht]".
iPoseProof "HkA" as "[_ HkA2]".
iPoseProof (resT_agree with "HkA1 HkA2") as "e".
rewrite res_equivI.
iDestruct "e" as "(->&->&eΦ)".
rewrite ofe_morO_equivI.
iRewrite ("eΦ" $! t) in "Ht".
wp_pures; wp_bind (term_proj _ _); iApply (wp_term_proj _ _ 0).
case etA': (Spec.proj t 0)=> [tA'|]; last by wp_pures; iExists None.
wp_pures; wp_bind (term_proj _ _); iApply (wp_term_proj _ _ 1).
case etB: (Spec.proj t 1)=> [tB|]; wp_pures; try by iExists None.
wp_bind (term_proj _ _); iApply (wp_term_proj _ _ 2).
case epkB': (Spec.proj t 2)=> [pkB'|]; wp_pures; try by iExists None.
wp_bind (eq_term _ _); iApply wp_eq_term.
case: bool_decide_reflect=> e; wp_pures; try by iExists None.
subst tA'.
wp_bind (eq_term _ _); iApply wp_eq_term.
case: bool_decide_reflect=> e; wp_pures; try by iExists None.
subst pkB'.
iDestruct "Ht" as "[Ht|(_&Ht)]"; last first.
  iPoseProof (proj_termT _ etA' with "Ht") as "contra".
  iDestruct "HtA" as "[_ #HtA]".
  by iPoseProof ("HtA" with "contra") as "%contra".
iDestruct "Ht" as "[#Hagent Ht]".
case: t etA' etB epkB'=> // tA' [] // tB' [] // pkB' t' enA' enB epkB'.
rewrite /= in enA' enB epkB'; move: enA' enB epkB'=> [->] [->] [->] {tA' tB' pkB'}.
iSimpl in "Hagent".
iMod (nsl_sess_update with "Hctx tok Hagent") as "[tok #?]"=> //.
iMod (term_session_auth_termT with "Hctx Hagent") as "[#HtB _]"=> //.
wp_bind (enc _ _).
iApply (twp_wp_step with "HtB"); iApply twp_enc.
iIntros "#HtB'"; iModIntro; wp_pures.
wp_bind (send _); iApply wp_send.
  rewrite /=. iExists Pub, Sec, _; iSplit.
    by iDestruct "HkB" as "[??]"; eauto.
  iLeft.
  iDestruct "Ht" as "(?&?&?&?)"; iSplit=> //.
  iModIntro; rewrite /=; iRight.
  by iExists kA, tA.
wp_pures; iExists (Some tB); by iSplit.
Qed.

Lemma wp_initiator_other kA kB (tA : term) l E lvl_dec Φ :
  ↑cryptoN.@"nsl" ⊆ E →
  symbols_of_term tA = {[l]} →
  nsl_ctx -∗
  stermT Pub tA -∗
  unregistered l -∗
  nsl_key Init kA -∗
  akeyT Pub lvl_dec Φ kB -∗
  WP initiator (TKey KADec kA) (TKey KAEnc kA) (TKey KAEnc kB) tA #() @ E
     {{v, ∃ onB : option term,
          ⌜v = repr onB⌝ ∗
          match onB with
          | Some tB => termT Pub tB
          | None => True
          end}}.
Proof.
rewrite /initiator.
iIntros (? Hfresh) "#Hctx #HtA Hown #HkA #HkB".
wp_pures; wp_bind (tuple _ _).
iApply wp_tuple.
wp_bind (enc _ _); iApply wp_enc.
wp_pures; wp_bind (send _); iApply wp_send.
  rewrite /=; iExists Pub, lvl_dec, Φ=> /=.
  iSplit; eauto.
  iRight; iSplit; rewrite /=; first by [].
  iSplit.
    by iDestruct "HtA" as "[??]".
  iExists Pub, (agent_pred Init kA); iSplit; last by iPureIntro.
  iExists Sec; by iDestruct "HkA" as "[??]".
wp_pures; wp_bind (recv _); iApply wp_recv.
iIntros (m2) "#Hm2".
wp_bind (dec _ _); iApply wp_dec.
case: m2; try by protocol_failure.
case; last by protocol_failure.
move=> k t /=.
case: decide=> [ {k}<-|ne]; last by wp_pures; iExists None.
iDestruct "Hm2" as (lvl_enc' lvl_dec' Φ') "[HkA1 Ht]".
iPoseProof "HkA" as "[_ HkA2]".
iPoseProof (resT_agree with "HkA1 HkA2") as "e".
rewrite res_equivI.
iDestruct "e" as "(->&->&eΦ)".
rewrite ofe_morO_equivI.
iRewrite ("eΦ" $! t) in "Ht".
wp_pures; wp_bind (term_proj _ _).
iApply (wp_term_proj _ _ 0).
case etA': (Spec.proj t 0)=> [tA'|]; last by wp_pures; iExists None.
wp_pures; wp_bind (term_proj _ _).
iApply (wp_term_proj _ _ 1).
case etB: (Spec.proj t 1)=> [tB|]; wp_pures; try by iExists None.
wp_bind (term_proj _ _); iApply (wp_term_proj _ _ 2).
case epkB': (Spec.proj t 2)=> [pkB'|]; wp_pures; try by iExists None.
wp_bind (eq_term _ _).
iApply wp_eq_term.
case: bool_decide_reflect=> e; wp_pures; try by iExists None.
subst tA'.
wp_bind (eq_term _ _); iApply wp_eq_term.
case: bool_decide_reflect=> e; wp_pures; try by iExists None.
subst pkB'.
case: t etA' etB epkB'=> // tA' [] // tB' [] // pkB' t' enA' enB epkB'.
rewrite /= in enA' enB epkB'; move: enA' enB epkB'=> [->] [->] [->] {tA' tB' pkB'}.
iDestruct "Ht" as "[Ht|(_&Ht)]".
  iDestruct "Ht" as "[#Hagent Ht]".
  iSimpl in "Hagent".
  iMod (term_session_auth_termT with "Hctx Hagent") as "/= [#HtB #HtA']"=> //.
  iMod (term_session_nsl_key with "Hctx Hagent") as "#HkB'"=> //.
  wp_bind (enc _ _).
  iApply wp_fupd.
  iApply wp_enc.
  iModIntro; wp_pures.
  iDestruct "HtA"  as "[HtA _]".
  iDestruct "HtA'" as "[_ #min]".
  by iPoseProof ("min" with "HtA") as "%".
wp_bind (enc _ _).
iApply wp_enc.
wp_pures; iSimpl in "Ht"; iDestruct "Ht" as "(_ & HtB & _)".
wp_bind (send _); iApply wp_send.
  iModIntro.
  rewrite /=; iExists Pub, lvl_dec, Φ; iSplit=> //.
  by iRight; iSplit.
wp_pures; by iExists (Some tB); eauto.
Qed.

End NSL.
