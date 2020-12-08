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

Definition initiator_pred p : iProp Σ :=
  match p.2 with
  | TPair nA (TPair nB (TPair (TKey KAEnc kB) _)) =>
    term_session_frag nB (Session Resp p.1 kB (Some nA))
  | _ => False
  end.

Global Instance initiator_pred_proper : NonExpansive initiator_pred.
Proof.
move=> n; case=> [??] [??] [/= ??].
solve_contractive.
Qed.

Definition responder_pred p : iProp Σ :=
  match p.2 with
  | TPair (TInt tag) m =>
    if decide (tag = 1) then
      match m with
      | TPair nA (TPair (TKey KAEnc kA) _) =>
        term_session_frag nA (Session Init kA p.1 None)
      | _ => False%I
      end
    else if decide (tag = 3) then
      match m with
      | TPair nB _ =>
        (∃ kA nA, term_session_frag nA (Session Init kA p.1 (Some nB)))%I
      | _ => False%I
      end
    else False%I
  | _ => False
  end.

Global Instance responder_pred_proper : NonExpansive responder_pred.
Proof.
move=> n; case=> [??] [??] [/= ??].
solve_contractive.
Qed.

Global Instance initiator_pred_persistent p :
  Persistent (initiator_pred p).
Proof.
case: p=> kA t.
case: t; try by move=> *; apply _.
move=> nA; case; try by move=> *; apply _.
move=> nB; case; try by move=> *; apply _.
case; try by move=> *; apply _.
by case; move=> *; apply _.
Qed.

Global Instance responder_pred_persistent p :
  Persistent (responder_pred p).
Proof.
rewrite /responder_pred.
case: p=> kB t /=.
case: t; try by move=> *; apply _.
case; try by move=> *; apply _.
move=> tag m.
case: (decide (tag = 1))=> // _.
  case: m; try by move=> *; apply _.
  move=> nA; do 3![case; try by move=> *; apply _].
case: (decide (tag = 3)) => //; try by apply _.
case: m; try by apply _.
Qed.

Definition agent_pred rl :=
  match rl with
  | Init => OfeMor initiator_pred
  | Resp => OfeMor responder_pred
  end.

Global Instance agent_pred_persistent rl p :
  Persistent (agent_pred rl p).
Proof. by case: rl; apply _. Qed.

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

Definition nsl_res : iProp Σ :=
  is_res nsl_init_name (RAKey Pub Sec (agent_pred Init)) ∗
  is_res nsl_resp_name (RAKey Pub Sec (agent_pred Resp)).

Lemma nsl_res_persistent : Persistent nsl_res.
Proof. apply _. Qed.

Definition nsl_key rl k : iProp Σ :=
  akeyT (role_name rl) Pub Sec (agent_pred rl) k.

Global Instance nsl_key_persistent rl k :
  Persistent (nsl_key rl k).
Proof. apply _. Qed.

Definition pub_enc_key γ k : iProp Σ :=
  ∃ lvl_dec Φ, akeyT γ Pub lvl_dec Φ k.

Global Instance pub_enc_key_persistent γ k : Persistent (pub_enc_key γ k).
Proof. apply _. Qed.

(* MOVE *)
Lemma is_res_agree γ r1 r2 :
  is_res γ r1 -∗ is_res γ r2 -∗ r1 ≡ r2.
Proof.
iIntros "#own1 #own2".
iPoseProof (own_valid_2 with "own1 own2") as "e".
by rewrite agree_validI agree_equivI.
Qed.

Lemma pub_enc_keyS rl k :
  nsl_res -∗
  pub_enc_key (role_name rl) k -∗
  nsl_key rl k.
Proof.
iIntros "[init resp]"; iDestruct 1 as (lvl_dec Φ) "[own key]".
by case: rl => /=; iSplit.
Qed.

Definition coherent_views SM t1 s1 : Prop :=
  match s1.(srole), s1.(sdata) with
  | Init, None => True
  | Init, Some t2 =>
    SM !! t2 = Some (Session Resp s1.(sinit) s1.(sresp) (Some t1))
  | Resp, None => False
  | Resp, Some _ => True
  end.

Definition nsl_data_for γ rl t :=
  stermT (if decide (γ = role_name rl) then
            Sec
          else Pub)
         t.

Global Instance nsl_data_for_persistent γ rl t :
  Persistent (nsl_data_for γ rl t).
Proof. apply _. Qed.

Definition session_inv SM : iProp Σ :=
  ∀ t1 s1, ⌜SM !! t1 = Some s1⌝ -∗
  ∃ γ,
    pub_enc_key γ (sother s1)
    ∗ registered t1
    ∗ nsl_data_for γ (sroleo s1) t1
    ∗ nsl_key s1.(srole) (sowner s1)
    ∗ ⌜coherent_views SM t1 s1⌝.

Lemma session_inv_unregistered SM t :
  unregistered t -∗
  session_inv SM -∗
  ⌜SM !! t = None⌝.
Proof.
iIntros "Hunreg Hinv".
destruct (SM !! t) as [s_t|] eqn:SM_t=> //.
iDestruct ("Hinv" $! _ _ SM_t) as (?) "(?&Hreg&?)".
by iDestruct (registered_unregistered with "Hreg Hunreg") as "[]".
Qed.

Definition nsl_inv : iProp Σ :=
  auth_inv nsl_sess_name to_session_map session_inv.

Definition nsl_ctx : iProp Σ :=
  auth_ctx nsl_sess_name (cryptoN.@"nsl") to_session_map session_inv.

Lemma nsl_sess_alloc γ kI kR t rl E ot :
  let kA := if rl is Init then kI else kR in
  let kB := if rl is Init then kR else kI in
  let s  := Session rl kI kR ot           in
  ↑cryptoN.@"nsl" ⊆ E →
  (if rl is Init then ot = None else is_Some ot) →
  nsl_ctx -∗
  nsl_key rl kA -∗
  unregistered t -∗
  pub_enc_key γ kB -∗
  nsl_data_for γ (sroleo s) t ={E}=∗
  term_session_auth t s ∗ term_session_frag t s.
Proof.
move=> kA kB s sub rl_ot; iIntros "#Hctx #Howner Hunreg #HkB #Ht".
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
  iExists γ.
  do 3![iSplit=> //].
  rewrite /s; iSplit=> //; case: (rl) rl_ot=> // rl_ot.
    by rewrite rl_ot.
  by case: rl_ot=> t' -> /=.
rewrite lookup_insert_ne //; iIntros (SM_t1').
iDestruct ("Hinv" $! _ _ SM_t1')
  as (γ') "(Hγ' & Hreg' & Ht1' & Howner' & %Hcoh)".
iExists γ'; iFrame; iPureIntro.
move: Hcoh; rewrite /coherent_views.
case: (srole s1') (sdata s1')=> [|] [t2'|] //.
case: (decide (t = t2'))=> [<-|?]; first by rewrite Hfresh.
by rewrite lookup_insert_ne.
Qed.

Lemma nsl_sess_alloc_init γ kA kB tA E :
  ↑cryptoN.@"nsl" ⊆ E →
  nsl_ctx -∗
  nsl_key Init kA -∗
  unregistered tA -∗
  pub_enc_key γ kB -∗
  nsl_data_for γ Resp tA ={E}=∗
  term_session_auth tA (Session Init kA kB None) ∗
  term_session_frag tA (Session Init kA kB None).
Proof.
iIntros (HE) "#Hctx #HkA Hunreg #HkB #HtA".
by iApply (nsl_sess_alloc with "Hctx HkA Hunreg HkB HtA").
Qed.

Lemma nsl_sess_alloc_resp γ kA kB tA tB E :
  ↑cryptoN.@"nsl" ⊆ E →
  nsl_ctx -∗
  nsl_key Resp kB -∗
  unregistered tB -∗
  pub_enc_key γ kA -∗
  nsl_data_for γ Init tB  ={E}=∗
  term_session_auth tB (Session Resp kA kB (Some tA)) ∗
  term_session_frag tB (Session Resp kA kB (Some tA)).
Proof.
iIntros (?) "#Hctx #HkB Hunreg #HkA #HtB".
by iApply (nsl_sess_alloc with "Hctx HkB Hunreg HkA HtB")=> /=; eauto.
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
  by iDestruct ("Hinv" $! _ _ SM_t) as (?) "(?&?&?&?&?)".
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
  iDestruct ("Hinv" $! _ _ SM_tA) as (γB) "(HγB & Hreg & Ht & Howner & %Hcoh)".
  iDestruct ("Hinv" $! _ _ SM_tB) as (γA) "(HγA & _ & Ht' & _ & _)".
  iExists γB.
  do 4![iSplit=> //]; iPureIntro.
  rewrite /s1' /=.
  by rewrite /coherent_views /= lookup_insert_ne // SM_tB.
rewrite lookup_insert_ne //.
iIntros "%SM_t"; iDestruct ("Hinv" $! _ _ SM_t) as (?) "(?&?&?&?&%Hcoh)".
iExists _; do 4![iSplit=> //]; iPureIntro.
move: Hcoh; rewrite /coherent_views.
case erole: (srole s)=> //.
case edata: (sdata s)=> [t'|] //.
case: (decide (tA = t'))=> [<-|?]; first by rewrite SM_tA.
by rewrite lookup_insert_ne.
Qed.

Variable send recv gen : val.

Definition msg1 : val := (λ: "nA" "pkA",
  tuple (TInt 1) (tuple "nA" (tuple "pkA" (TInt 0)))
).

Definition msg1_spec nA pkA :=
  TPair (TInt 1) (TPair nA (TPair pkA (TInt 0))).

(* MOVE *)
Lemma termT_aenc_pub_pub γ lvl Φ k t :
  akeyT γ Pub lvl Φ k -∗
  termT Pub t -∗
  termT Pub (TEnc true k t).
Proof.
rewrite {2}termT_eq /= -termT_eq.
iIntros "#Hk #Ht"; by iExists γ, Pub, lvl, Φ; eauto.
Qed.

Lemma termT_aenc_pub_sec γ Φ k t :
  akeyT γ Pub Sec Φ k -∗
  □ Φ (k, t) -∗
  termT Sec t -∗
  termT Pub (TEnc true k t).
Proof.
rewrite {2}termT_eq /= -termT_eq.
iIntros "#Hk #Φt #Ht".
by iExists γ, Pub, Sec, Φ; eauto.
Qed.

Lemma enc_msg1 γ kA kB nA m1 :
  Spec.enc (TKey KAEnc kB) (msg1_spec nA (TKey KAEnc kA)) = Some m1 →
  nsl_res -∗
  nsl_key Init kA -∗
  pub_enc_key γ kB -∗
  nsl_data_for γ Resp nA -∗
  termT Pub m1.
Proof.
rewrite /=; case=> <- {m1}.
iIntros "#Hres #HkA #HkB #HnA".
rewrite /nsl_data_for.
case: (decide _) => [->|].
  iPoseProof (pub_enc_keyS with "Hres HkB") as "{HkB} HkB".
  iApply termT_aenc_pub_sec; eauto; last first.
    rewrite termT_eq /= -termT_eq.



Lemma wp_msg1 (nA pkA : term) E Ψ :
  Ψ (repr (msg1_spec nA pkA)) -∗
  WP msg1 nA pkA @ E {{ Ψ }}.
Proof.
iIntros "H".
rewrite /msg1; wp_pures.
wp_bind (tuple pkA _); iApply wp_tuple.
wp_bind (tuple nA _); iApply wp_tuple.
by iApply wp_tuple.
Qed.

Definition get_msg1 : val := (λ: "m",
  bind: "tag" := term_proj "m" #0 in
  bind: "tag" := as_int "tag" in
  if: "tag" = #1 then
    bind: "nA" := term_proj "m" #1 in
    bind: "pkA" := term_proj "m" #2 in
    SOME ("nA", "pkA")
  else NONE).

Definition get_msg1_spec t :=
  match t with
  | TPair (TInt tag) m =>
    if decide (tag = 1) then
      if m is TPair nA (TPair pkA _) then Some (nA, pkA)
      else None
    else None
  | _ => None
  end.

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None).

Lemma wp_get_msg1 t E Ψ :
  Ψ (repr (get_msg1_spec t)) -∗
  WP get_msg1 t @ E {{ Ψ }}.
Proof.
rewrite /get_msg1; iIntros "Hpost"; wp_pures.
wp_bind (term_proj _ _); iApply (wp_term_proj _ _ 0).
case: t; try by move=> *; wp_pures; eauto.
move=> tag t; wp_pures; wp_bind (as_int _); iApply wp_as_int.
case: tag; try by move=> *; wp_pures; eauto.
move=> /= tag; wp_pures.
case: (bool_decide_reflect (repr tag = #1)) => [[->]|d] /=.
  wp_pures.
  wp_bind (term_proj _ _); iApply (wp_term_proj _ _ 1).
  case: t; try by move=> *; wp_pures; eauto.
  move=> nA m /=; wp_pures.
  wp_bind (term_proj _ _); iApply (wp_term_proj _ _ 2).
  by case: m; try by move=> *; wp_pures; eauto.
case: decide d=> [-> //|] _ _.
by wp_pures.
Qed.

Definition msg3 : val := (λ: "nB",
  tuple (TInt 3) (tuple "nB" (TInt 0))
).

Definition msg3_spec nB :=
  TPair (TInt 3) (TPair nB (TInt 0)).

Lemma wp_msg3 (nB : term) E Ψ :
  Ψ (repr (msg3_spec nB)) -∗
  WP msg3 nB @ E {{ Ψ }}.
Proof.
iIntros "H".
rewrite /msg3; wp_pures.
wp_bind (tuple nB _); iApply wp_tuple.
by iApply wp_tuple.
Qed.

Definition get_msg3 : val := (λ: "m",
  bind: "tag" := term_proj "m" #0 in
  bind: "tag" := as_int "tag" in
  if: "tag" = #3 then term_proj "m" #1
  else NONE).

Definition get_msg3_spec t :=
  match t with
  | TPair (TInt tag) m =>
    if decide (tag = 3) then Spec.proj m 0
    else None
  | _ => None
  end.

Lemma wp_get_msg3 t E Ψ :
  Ψ (repr (get_msg3_spec t)) -∗
  WP get_msg3 t @ E {{ Ψ }}.
Proof.
rewrite /get_msg3; iIntros "Hpost"; wp_pures.
wp_bind (term_proj _ _); iApply (wp_term_proj _ _ 0).
case: t; try by move=> *; wp_pures; eauto.
move=> tag t; wp_pures; wp_bind (as_int _); iApply wp_as_int.
case: tag; try by move=> *; wp_pures; eauto.
move=> /= tag; wp_pures.
case: (bool_decide_reflect (repr tag = #3)) => [[->]|d] /=.
  wp_pures.
  by iApply (wp_term_proj _ _ 1).
case: decide d=> [-> //|] _ _.
by wp_pures.
Qed.

Definition initiator (skA pkA pkB nA : val) : val := λ: <>,
  bind: "m1"   := enc pkB (msg1 nA pkA) in
  send "m1";;
  bind: "m2"   := dec skA (recv #()) in
  bind: "nA'"  := term_proj "m2" #0 in
  bind: "nB"   := term_proj "m2" #1 in
  bind: "pkB'" := term_proj "m2" #2 in
  if: eq_term "nA'" nA && eq_term "pkB'" pkB then
    bind: "m3" := enc pkB (msg3 "nB") in
    send "m3";;
    SOME "nB"
  else NONE.

Definition responder (skB pkB : val) : val := λ: <>,
  bind: "m1" := dec skB (recv #()) in
  bind: "m1" := get_msg1 "m1" in
  let: "nA" := Fst "m1" in
  let: "pkA" := Snd "m1" in
  bind: "kt" := is_key "pkA" in
  if: "kt" = repr KAEnc then
    let: "nB" := gen #() in
    bind: "m2" := enc "pkA" (tuple "nA" (tuple "nB" (tuple pkB (TInt 0)))) in
    send "m2";;
    bind: "m3" := dec skB (recv #()) in
    bind: "nB'" := get_msg3 "m3" in
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

Lemma tc1 kA kB (tA : term) :
  own nsl_resp_name (Some (to_agree (agent_pred Resp))) -∗
  nsl_data_for Resp kB tA -∗
  nsl_key Init kA -∗
  term_session_frag tA (Session Init kA kB None) -∗
  termT Pub (TEnc true kB (msg1_spec tA (TKey KAEnc kA))).
Proof.
iIntros "#Hresp HtA HkA #frag".
iDestruct "HtA" as (lvl) "[HtA HkB]".
iDestruct "HkB" as (lvl_dec γ Φ) "[#HkB %e]".
case: lvl e => e.
- rewrite /=.
  iExists Pub, lvl_dec, _, _ => /=.
  iSplit; eauto.
  iRight.
  iSplit => //.
  iSplit => //.
  iSplit; first by iDestruct "HtA" as "[??]".
  iSplit=> //.
  iExists Pub, _, _; iSplit => //.
  by iExists _; eauto.
- have {}/e [??] := eq_refl Sec; subst lvl_dec γ.
  iAssert (nsl_key Resp kB) as "{HkB} HkB".
    by iDestruct "HkB" as "[??]"; iSplit.
  rewrite /=.
  iExists Pub, _, _, _.
  iSplit; eauto.
  iLeft.
  iSplit; first by iModIntro.
  iSplit=> //.
  iSplit; first by iDestruct "HtA" as "[??]".
  iSplit=> //.
  iExists Pub, _, _.
  by iSplit; eauto.
Qed.

(* MOVE *)
Lemma stermTS lvl t :
  termT Pub t -∗
  stermT lvl t -∗
  ⌜lvl = Pub⌝.
Proof.
iIntros "Ht1 [Ht2 #Hmin]".
iSpecialize ("Hmin" with "Ht1").
by case: lvl.
Qed.

Global Instance akeyT_Proper n :
  Proper ((=) ==> (=) ==> (=) ==> dist n ==> (=) ==> dist n) akeyT.
Proof. solve_proper. Qed.
Lemma wp_initiator kA kB (tA : term) lvl_dec γ Φ E Ψ :
  ↑cryptoN.@"nsl" ⊆ E →
  let is_sec := bool_decide (γ = nsl_resp_name ∧ lvl_dec = Sec) in
  nsl_ctx -∗
  own nsl_resp_name (Some (to_agree (agent_pred Resp))) -∗
  nsl_data_for Resp kB tA -∗
  unregistered tA -∗
  nsl_key Init kA -∗
  akeyT Pub lvl_dec γ Φ kB -∗
  (∀ onB : option term,
      (if onB is Some tB then
         if is_sec then
           term_session_auth tA (Session Init kA kB (Some tB)) ∗
           term_session_frag tB (Session Resp kA kB (Some tA))
         else termT Pub tB
       else True) -∗
      Ψ (repr onB)) -∗
  WP initiator (TKey KADec kA) (TKey KAEnc kA) (TKey KAEnc kB) tA #() @ E
     {{ Ψ }}.
Proof.
rewrite /initiator.
iIntros (?) "#Hctx #Hown #HtA Hl #HkA #HkB Hpost".
wp_pures; wp_bind (msg1 _ _); iApply wp_msg1.
iMod (nsl_sess_alloc_init kA kB with "Hctx HkA Hl HtA") as "[tok #Hfrag]"=> //.
wp_bind (enc _ _); iApply wp_enc; wp_pures.
wp_bind (send _); iApply wp_send.
  by iModIntro; iApply tc1; eauto.
wp_pures; wp_bind (recv _); iApply wp_recv.
iIntros (m2) "#Hm2".
wp_bind (dec _ _); iApply wp_dec.
case: m2; try by protocol_failure.
case; last by protocol_failure.
move=> k t; rewrite /=.
case: decide=> [ {k}<-|ne]; last by protocol_failure.
iDestruct "Hm2" as (lvl_enc' lvl_dec' γ' Φ') "[HkA1 Ht]".
iPoseProof (akeyT_agree with "HkA1 HkA") as "(->&->&->&e)".
rewrite ofe_morO_equivI.
iRewrite ("e" $! (kA, t)) in "Ht".
iClear "HkA1 e".
wp_pures; wp_bind (term_proj _ _); iApply (wp_term_proj _ _ 0).
case etA': (Spec.proj t 0)=> [tA'|]; last by protocol_failure.
wp_pures; wp_bind (term_proj _ _); iApply (wp_term_proj _ _ 1).
case etB: (Spec.proj t 1)=> [tB|]; last by protocol_failure.
wp_pures; wp_bind (term_proj _ _); iApply (wp_term_proj _ _ 2).
case epkB': (Spec.proj t 2)=> [pkB'|]; last by protocol_failure.
wp_pures; wp_bind (eq_term _ _); iApply wp_eq_term.
case: (bool_decide_reflect (tA' = tA)) => e; last by protocol_failure.
subst tA'.
wp_pures; wp_bind (eq_term _ _); iApply wp_eq_term.
case: (bool_decide_reflect (pkB' = _)) => e; last by protocol_failure.
wp_pures; subst pkB'.
iDestruct "Ht" as "[Ht|(_&Ht)]"; last first.
  iPoseProof (proj_termT _ etB with "Ht") as "HtB".
  wp_bind (msg3 _); iApply wp_msg3.
  wp_bind (enc _ _); iApply wp_enc; wp_pures.
  wp_bind (send _); iApply wp_send.
    iModIntro => /=.
    iExists _, lvl_dec, _, _; iSplit => //.
    by eauto.
  wp_pures.
  iApply ("Hpost" $! (Some tB)).
  case: bool_decide_reflect=> // - [??]; subst γ lvl_dec.
  iPoseProof (proj_termT _ etA' with "Ht") as "HtA'".
  iDestruct "HtA" as (lvl') "[HtA contra]".
  case: lvl'; last first.
    iDestruct "HtA" as "[_ #HtA]".
    by iSpecialize ("HtA" with "HtA'").
  rewrite /nsl_key /=.
  (* TODO: Extract as separate lemma *)
  iPoseProof "HkB" as "[_ HownB]".
  iPoseProof (own_valid_2 with "Hown HownB") as "HΦ".
  rewrite /= -Some_op uPred.option_validI agree_validI agree_equivI.
  iRewrite -"HΦ" in "HkB".
  iDestruct "contra" as (lvl_dec γ Φ'') "[HkB' %e]".
  iPoseProof (akeyT_agree with "HkB' HkB") as "(_ & -> & -> & ?)".
  by have // : Pub = Sec by apply/e.
iDestruct "Ht" as "[#Hagent Ht]".
case: t etA' etB epkB'=> // tA' [] // tB' [] // pkB' t' enA' enB epkB'.
rewrite /= in enA' enB epkB'; move: enA' enB epkB'=> [->] [->] [->] {tA' tB' pkB'}.
iSimpl in "Hagent".
iClear "Hfrag".
iMod (nsl_sess_update with "Hctx tok Hagent") as "[tok #Hfrag]"=> //.
rewrite /=.
wp_bind (msg3 _); iApply wp_msg3.
wp_bind (enc _ _).
iDestruct "Ht" as "(HtA'&HtB&_&_)".
iApply (twp_wp_step with "HtB"); iApply twp_enc.
iIntros "_"; iModIntro; wp_pures.
rewrite /sroleo /sother /initiator_pred /=.
iMod (term_session_nsl_key with "Hctx Hagent") as "#HkB'" => //.
rewrite /sowner /=.
iAssert (▷ (⌜Pub = Pub⌝ ∗
            ⌜lvl_dec = Sec⌝ ∗
            ⌜γ = nsl_resp_name⌝ ∗
            Φ ≡ agent_pred Resp))%I as "(_ & >% & >% & _)".
  by iModIntro; iApply akeyT_agree.
subst γ lvl_dec. iClear "HkB". iRename "HkB'" into "HkB".
wp_bind (send _); iApply wp_send.
  iModIntro.
  rewrite /=. iExists Pub, Sec, _, _; iSplit; eauto.
  iLeft; iSplit => //.
    iModIntro.
    rewrite /= {2}/responder_pred /=.
    by iExists kA, tA.
  eauto.
wp_pures; iApply ("Hpost" $! (Some tB)).
by rewrite bool_decide_eq_true_2 //; iSplit.
Qed.

Lemma wp_responder kB E Ψ :
  ↑cryptoN.@"nsl" ⊆ E →
  nsl_ctx -∗
  own nsl_init_name (Some (to_agree (agent_pred Init))) -∗
  nsl_key Resp kB -∗
  (∀ ot : option (term * term * term),
      (if ot is Some (pkA, nA, nB) then
         ∃ kA, ⌜pkA = TKey KAEnc kA⌝ ∗
               (nsl_key Init kA -∗
                term_session_frag nA (Session Init kA kB (Some nB)) ∗
                term_session_auth nB (Session Resp kA kB (Some nA)))
       else True) -∗
       Ψ (repr ot)) -∗
  WP responder (TKey KADec kB) (TKey KAEnc kB) #() @ E {{ Ψ }}.
Proof.
rewrite /responder.
iIntros (?) "#Hctx #Hown #HkB Hpost".
wp_pures; wp_bind (recv _); iApply wp_recv; iIntros (t) "Ht".
wp_bind (dec _ _); iApply wp_dec.
case: t; try by protocol_failure.
move=> is_sym k t; case: is_sym; try by protocol_failure.
rewrite /=.
case: (decide (kB = k)); last by protocol_failure.
move=> <- {k}.
wp_pures.
iDestruct "Ht" as (lvl_enc lvl_dec γ Φ) "[#HkB' #Ht]".
iDestruct (akeyT_agree with "HkB' HkB") as "(-> & -> & -> & e)".
rewrite ofe_morO_equivI.
iRewrite ("e" $! (kB, t)) in "Ht".
iClear (Φ) "e HkB'".
wp_pures.
wp_bind (get_msg1 _); iApply wp_get_msg1.
case: t; try by protocol_failure.
case; try by protocol_failure.
move=> tag /=.
case: (decide _)=> [ {tag}->|?]; last by protocol_failure.
case; try by protocol_failure.
move=> nA; case; try by protocol_failure.
move=> pkA t.
wp_pures.
wp_bind (is_key _); iApply wp_is_key.
case: pkA; try protocol_failure.
move=> kt kA; wp_pures.
case: bool_decide_reflect; try by protocol_failure.
case: kt=> // _.
wp_pures.
iDestruct "Ht" as "[[#Hinv Ht] | [_ Ht]]"; last first.
  iPoseProof (proj_termT _ et0 with "Ht") as "HtA".
  iPoseProof (proj_termT _ et1 with "Ht") as "HkA".
  iDestruct "HkA" as (lvl' γ Φ') "[HkA %Hlvl']".
  case: lvl' Hlvl'=> //= _.
  iDestruct "HkA" as (lvl_dec) "HkA".
  pose (is_sec := lvl_dec = Sec ∧ γ = nsl_init_name).
  wp_bind (gen _); iApply (wp_gen _ (if bool_decide is_sec then Sec else Pub)).
  iIntros (tB) "unreg #HtB".
  iAssert (nsl_data_for Init kA tB) as "HtB'".
    iExists _; iSplit=> //.
    rewrite /is_sec; case: bool_decide_reflect.
      case=> -> ->.
      by iExists Sec, nsl_init_name, _; iSplit; eauto.
    move=> contra.
    by iExists lvl_dec, γ, Φ'; iSplit.
  iMod (nsl_sess_alloc_resp _ _ tA with "Hctx HkB unreg HtB'")
      as "[Hauth #Hfrag]" => //.
  wp_pures.
  wp_bind (tuple _ (TInt 0)); iApply wp_tuple.
  wp_bind (tuple tB _); iApply wp_tuple.
  wp_bind (tuple (repr tA) _); iApply wp_tuple.
  wp_bind (enc _ _); iApply wp_enc.
  wp_pures.
  wp_bind (send _); iApply wp_send.
    iModIntro.
    rewrite /=.
    case: bool_decide_reflect=> [[??]|not_sec].
    - subst lvl_dec γ.
      iAssert (nsl_key Init kA) as "{HkA} HkA".
      by iDestruct "HkA" as "[??]"; iSplit.
      iExists _, _, _, _; iSplitL; eauto.
      iLeft.
      iSplit=> //.
      iSplit; first by iApply (sub_termT with "HtA").
      iSplit; first by iDestruct "HtB" as "[??]".
      iSplit=> //.
      by iExists Pub, _, _; iSplit; eauto.
    - iExists _, _, _, _; iSplitL; eauto.
      iRight.
      iSplit=> //.
      iSplit=> //.
      iSplit; first by iDestruct "HtB" as "[??]".
      iSplit=> //.
      by iExists _, _, _; iSplit; eauto.
  wp_pures.
  wp_bind (recv _); iApply wp_recv.
  iIntros (t') "#Ht'".
  wp_bind (dec _ _); iApply wp_dec.
  case: t'; try by protocol_failure.
  case; try by protocol_failure.
  move=> k t' /=.
  case: (decide _)=> ?; try by protocol_failure.
  subst k.
  wp_pures.
  wp_bind (eq_term _ _); iApply wp_eq_term.
  case: (bool_decide_reflect (t' = tB)); try by protocol_failure.
  move=> {t'}->.
  wp_pures.
  iApply ("Hpost" $! (Some (_, _, _)) with "[Hauth]").
  iExists _; iSplitL; eauto.
  iIntros "#HkA'".
  rewrite /is_sec.
  iDestruct (akeyT_agree with "HkA HkA'") as "(_ & -> & -> & _)".
  rewrite bool_decide_eq_true_2 //.
  iDestruct "Ht'" as (??? Φ) "(HkB' & Ht')".
  iDestruct (akeyT_agree with "HkB' HkB") as "(-> & -> & -> & e)".
  rewrite ofe_morO_equivI.
  iRewrite ("e" $! (kB, tB)) in "Ht'".
  iClear (Φ) "HtB' HkB' e".
  iDestruct "Ht'" as "[[#Ht' _] | [_ HtB']]"; last first.
    iDestruct "HtB" as "[_ #Hmin]".
    by iPoseProof ("Hmin" with "HtB'") as "%".
  rewrite /=.
  pose (is_sec := bool_decide (lvl_dec = Sec ∧ γ = nsl_init_name)).
  wp_bind (gen _); iApply (wp_gen _ (if is_sec then Sec else Pub)).
  iIntros (tB) "unreg #HtB".
  iAssert (nsl_data_for Init kA tB) as "{HtB} HtB".
    iExists _; iSplit=> //.
    rewrite /is_sec; case: bool_decide_reflect.
      case=> -> ->.
      by iExists Sec, nsl_init_name, _; iSplit; eauto.
    move=> contra.
    by iExists lvl_dec, γ, Φ'; iSplit.
  iMod (nsl_sess_alloc_resp _ _ tA with "Hctx HkB unreg HtB")
      as "[Hauth #Hfrag]" => //.
  wp_pures.
  wp_bind (tuple _ (TInt 0)); iApply wp_tuple.
  wp_bind (tuple tB _); iApply wp_tuple.
  wp_bind (tuple (repr tA) _); iApply wp_tuple.
  wp_bind (enc _ _); iApply wp_enc.
  wp_pures.
  wp_bind (send _); iApply wp_send.
    iModIntro.
    rewrite /=.
    iExists _, _, _, _; iSplitL; eauto.
    iRight.
    iSplit=> //.
    iSplit=> //.
    iSplit=> //.
        iSplit=> //.
        by iExists _, _, _; iSplit; eauto.
      wp_pures.
      wp_bind (recv _); iApply wp_recv.
      iIntros (t') "#Ht'".
      wp_bind (dec _ _); iApply wp_dec.
      case: t'; try by protocol_failure.
      case; try by protocol_failure.
      move=> k t' /=.
      case: (decide _)=> ?; try by protocol_failure.
      subst k.
      wp_pures.
      wp_bind (eq_term _ _); iApply wp_eq_term.
      case: bool_decide_reflect; try by protocol_failure.
      move=> {t'}->.
      wp_pures.


iIntros (tB).


iDestruct "Ht" as "[Ht | (_ & Ht)]"; last first.
  wp_bind (term_proj _ _).
*)


End NSL.
