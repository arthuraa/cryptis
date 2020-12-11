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
  ∃ nA nB kB,
    ⌜p.2 = Spec.of_list [nA; nB; TKey KAEnc kB]⌝ ∗
    term_session_frag nB (Session Resp p.1 kB (Some nA)).

Global Instance initiator_pred_proper : NonExpansive initiator_pred.
Proof.
move=> n; case=> [??] [??] [/= ??].
solve_contractive.
Qed.

Definition msg1_spec nA pkA :=
  TPair (TInt 1) (TPair nA (TPair pkA (TInt 0))).

Definition responder1_pred p : iProp Σ :=
  ∃ nA kA, ⌜p.2 = Spec.of_list [nA; TKey KAEnc kA]⌝ ∗
           term_session_frag nA (Session Init kA p.1 None).

Global Instance responder1_pred_proper : NonExpansive responder1_pred.
Proof.
move=> n; case=> [??] [??] [/= ??].
solve_contractive.
Qed.

Global Instance responder1_pred_persistent p : Persistent (responder1_pred p).
Proof. apply _. Qed.

Definition responder2_pred p : iProp Σ :=
  ∃ nA kA,
    term_session_frag nA (Session Init kA p.1 (Some p.2)) ∗
    term_session_frag p.2 (Session Resp kA p.1 (Some nA)).

Global Instance responder2_pred_proper : NonExpansive responder2_pred.
Proof.
move=> n; case=> [??] [??] [/= ??].
solve_contractive.
Qed.

Global Instance responder2_pred_persistent p : Persistent (responder2_pred p).
Proof. apply _. Qed.

Definition responder_pred p : iProp Σ :=
  tagged_inv [(λne x, responder1_pred x);
              (λne x, responder2_pred x)] p.

Global Instance responder_pred_proper : NonExpansive responder_pred.
Proof. solve_contractive. Qed.

Global Instance initiator_pred_persistent p :
  Persistent (initiator_pred p).
Proof.
case: p=> kA t.
case: t; try by move=> *; apply _.
Qed.

Global Instance responder_pred_persistent p :
  Persistent (responder_pred p).
Proof.
apply tagged_inv_persistent.
case => /= [?? [<-]|] /=; first by apply _.
case => /= [?? [<-]|] /=; first by apply _.
by case.
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

Global Instance session_inv_persistent SM : Persistent (session_inv SM).
Proof. apply _. Qed.

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

Arguments sroleo !_ /.
Arguments sother !_ /.
Arguments sowner !_ /.

Lemma pub_enc_keyS' γ k rl :
  nsl_ctx -∗
  pub_enc_key γ k -∗
  nsl_key rl k -∗
  ⌜γ = role_name rl⌝.
Proof.
iIntros "ctx pub_k nsl_k".
iDestruct "pub_k" as (??) "pub_k".
by iDestruct (akeyT_agree with "pub_k nsl_k") as "(-> & ?)".
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

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None).

Definition initiator (skA pkA pkB nA : val) : val := λ: <>,
  bind: "m1"   := enc pkB (tag 0 (term_of_list [nA; pkA])) in
  send "m1";;
  bind: "m2"   := dec skA (recv #()) in
  bind: "m2"   := list_of_term "m2" in
  bind: "nA'"  := "m2" !! #0 in
  bind: "nB"   := "m2" !! #1 in
  bind: "pkB'" := "m2" !! #2 in
  if: eq_term "nA'" nA && eq_term "pkB'" pkB then
    bind: "m3" := enc pkB (tag 1 "nB") in
    send "m3";;
    SOME "nB"
  else NONE.

Definition responder (skB pkB : val) : val := λ: <>,
  bind: "m1" := dec skB (recv #()) in
  bind: "m1" := untag 0 "m1" in
  bind: "m1" := list_of_term "m1" in
  bind: "nA" := "m1" !! #0 in
  bind: "pkA" := "m1" !! #1 in
  bind: "kt" := is_key "pkA" in
  if: "kt" = repr KAEnc then
    let: "nB" := gen #() in
    let: "m2" := term_of_list ["nA"; "nB"; pkB] in
    bind: "m2" := enc "pkA" "m2" in
    send "m2";;
    bind: "m3" := dec skB (recv #()) in
    bind: "nB'" := untag 1 "m3" in
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

Lemma termT_msg1 γ kA kB (tA : term) :
  nsl_res -∗
  nsl_key Init kA -∗
  nsl_data_for γ Resp tA -∗
  pub_enc_key γ kB -∗
  term_session_frag tA (Session Init kA kB None) -∗
  termT Pub (TEnc true kB (Spec.tag 0 (Spec.of_list [tA; TKey KAEnc kA]))).
Proof.
iIntros "#Hres #HkA #HtA #HkB #frag".
destruct (decide (γ = role_name Resp)) as [->|e].
  iPoseProof (pub_enc_keyS with "Hres HkB") as "{HkB} #HkB".
  iApply (termT_aenc_pub_sec with "HkB").
  - rewrite /=.
    iModIntro.
    iApply tagged_inv_intro => //=.
    by rewrite /responder1_pred; eauto.
  - iApply termT_tag.
    iApply termT_of_list.
    rewrite /=; iSplit.
    + by rewrite /nsl_data_for /= decide_True //; iDestruct "HtA" as "[??]".
    + iSplit=> //; iApply (@sub_termT _ _ _ Pub) => //.
      by iApply termT_kenc; eauto.
iPoseProof "HkB" as (??) "H"; iApply (termT_aenc_pub_pub); eauto.
iApply termT_tag; iApply termT_of_list; rewrite /=; iSplit.
  by rewrite /nsl_data_for /= decide_False //; iDestruct "HtA" as "[??]".
by iSplit => //; iApply termT_kenc; eauto.
Qed.

Lemma wp_initiator kA kB (tA : term) γ E Ψ :
  ↑cryptoN.@"nsl" ⊆ E →
  let is_sec := bool_decide (γ = nsl_resp_name) in
  nsl_ctx -∗
  nsl_res -∗
  nsl_data_for γ Resp tA -∗
  unregistered tA -∗
  nsl_key Init kA -∗
  pub_enc_key γ kB -∗
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
wp_list (_ :: _ :: []).
wp_term_of_list.
wp_tag.
wp_enc.
iMod (nsl_sess_alloc_init γ kA kB with "Hctx HkA Hl HkB HtA") as "[auth #frag]"=> //.
wp_pures; wp_bind (send _); iApply wp_send.
  by iModIntro; iApply termT_msg1.
wp_pures; wp_bind (recv _); iApply wp_recv.
iIntros (m2) "#Hm2"; wp_dec m2; last protocol_failure.
wp_list_of_term m2; last protocol_failure.
wp_lookup nA' enA'; last protocol_failure.
wp_lookup nB  enB; last protocol_failure.
wp_lookup pkB' epkB'; last protocol_failure.
wp_eq_term e; last protocol_failure; subst nA'.
wp_eq_term e; last protocol_failure; subst pkB'.
wp_tag.
wp_enc.
iPoseProof (termT_adec_pub with "Hm2 [//]") as "{Hm2} [#Hm2|#Hm2]".
  iPoseProof (termT_of_listE with "Hm2") as "{Hm2} Hm2".
  iPoseProof (big_sepL_lookup with "Hm2") as "H0"; first exact: enA'.
  iPoseProof (big_sepL_lookup with "Hm2") as "H1"; first exact: enB.
  iPoseProof (big_sepL_lookup with "Hm2") as "H2"; first exact: epkB'.
  iClear (enA' enB epkB') "Hm2".
  wp_pures; wp_bind (send _); iApply wp_send.
    iModIntro.
    iDestruct "HkB" as (??) "HkB".
    iApply termT_aenc_pub_pub => //.
    by iApply termT_tag.
  wp_pures; iApply ("Hpost" $! (Some nB)).
  rewrite /nsl_data_for bool_decide_decide.
  case: decide => // ?; subst γ.
  iDestruct "HtA" as "[_ #HtA]".
  by iPoseProof ("HtA" with "H0") as "%".
iDestruct "Hm2" as "[#Hprot Hm2]".
iDestruct "Hprot" as (nA' nB' kB') "[%Hm2 frag']".
move/Spec.of_list_inj in Hm2; subst m2.
case: enA' enB epkB' => [] -> [] -> [] -> /=.
iPoseProof (termT_of_listE with "Hm2") as "{Hm2} Hm2".
iSimpl in "Hm2"; iDestruct "Hm2" as "(H0 & H1 & H2 & _)".
iMod (nsl_sess_update with "Hctx auth frag'") as "{frag} [tok #frag]"=> //=.
iMod (term_session_nsl_key with "Hctx frag'") as "#HkB'" => //=.
wp_pures; wp_bind (send _); iApply wp_send.
  iModIntro.
  iApply termT_aenc_pub_sec; eauto.
    by iModIntro; iApply tagged_inv_intro; eauto; iExists tA, kA; iSplit.
  by iApply termT_tag.
wp_pures; iApply ("Hpost" $! (Some nB)).
iPoseProof (pub_enc_keyS' with "Hctx HkB HkB'") as "%"; subst γ.
rewrite bool_decide_decide decide_True //.
by iSplit.
Qed.

Lemma wp_responder kB E Ψ :
  ↑cryptoN.@"nsl" ⊆ E →
  nsl_ctx -∗
  nsl_res -∗
  nsl_key Resp kB -∗
  (∀ ot : option (term * term * term),
      (if ot is Some (pkA, nA, nB) then
         ∃ γ kA,
           ⌜pkA = TKey KAEnc kA⌝ ∗
           pub_enc_key γ kA ∗
           termT Sec nA ∗
           termT Sec nB ∗
           (nsl_key Init kA -∗
            term_session_frag nA (Session Init kA kB (Some nB)) ∗
            term_session_auth nB (Session Resp kA kB (Some nA)))
       else True) -∗
       Ψ (repr ot)) -∗
  WP responder (TKey KADec kB) (TKey KAEnc kB) #() @ E {{ Ψ }}.
Proof.
iIntros (?) "#Hctx #Hres #HkB Hpost".
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
iDestruct (termT_adec_pub_sec with "Hm1 [//]") as (lm1) "{Hm1} [Hm1 Hprot]".
iPoseProof (termT_untag with "Hm1") as "{Hm1} Hm1".
iPoseProof (termT_of_listE with "Hm1") as "{Hm1} Hm1".
iPoseProof (big_sepL_lookup with "Hm1") as "HnA"; first exact: enA.
iPoseProof (big_sepL_lookup with "Hm1") as "HpkA"; first exact: epkA.
pose Pm1 := term_session_frag nA (Session Init kA kB None).
iAssert (guarded lm1 Pm1) as "{Hprot} Hprot".
  iApply (guarded_mono with "Hprot").
  iIntros "!> {Hprot} #Hprot".
  iPoseProof (tagged_inv_elim' with "Hprot") as "{Hprot} Hprot".
  iDestruct "Hprot" as (nA' kA') "/= [%em1 #frag]".
  move/Spec.of_list_inj in em1; subst m1.
  by case: enA epkA => [] -> [] -> {nA' kA'}.
iAssert (|={E}=> ▷ ∃ γ, pub_enc_key γ kA ∗ guarded lm1 (⌜γ = role_name Init⌝))%I as "{HpkA} > #HpkA".
  case: lm1 => /=.
    do 2!iModIntro.
    iDestruct (termT_TAEncE with "HpkA") as (γ) "H".
    by iExists γ; iSplit.
  iMod (term_session_nsl_key with "Hctx Hprot") as "{Hprot} # Hprot" => //.
  do 2!iModIntro; iExists (role_name Init); iSplit; eauto.
  by iExists _, _; eauto.
wp_pures.
iDestruct "HpkA" as (γ) "[HkA Hγ]".
pose (lm2 := if decide (γ = role_name Init) then Sec else Pub).
iAssert (⌜lm1 ⊑ lm2⌝)%I as "%lm1_lm2".
  rewrite /lm2; case: lm1 => //=.
  by iDestruct "Hγ" as "->"; rewrite decide_True //.
iAssert (guarded lm2 (nsl_key Init kA)) as "HkAG".
  rewrite /lm2; case: decide => // ->.
  by iApply pub_enc_keyS.
wp_pures; wp_bind (gen _); iApply (wp_gen _ lm2); iIntros (nB) "unreg #HnB".
wp_list (_ :: _ :: _ :: []); wp_term_of_list; wp_enc; wp_pures.
set m2 := Spec.of_list [nA; nB; TKey KAEnc kB].
set sB := Session Resp kA kB (Some nA).
iAssert (|={E}=> guarded lm2 (term_session_frag nB sB ∗ term_session_auth nB sB))%I
    with "[unreg]" as "> [#Hfrag Hauth]".
  rewrite /lm2; case: decide => [->|_]; last by iModIntro.
  iAssert (nsl_data_for (role_name Init) Init nB) as "{HnB} HnB".
    by rewrite /nsl_data_for decide_True //.
  iMod (nsl_sess_alloc_resp _ kA kB nA with "Hctx HkB unreg HkA HnB")
    as "[auth #frag]"=> //=.
  by iModIntro; iSplit.
iAssert (termT lm2 nA) as "{HnA} HnA"; first by iApply sub_termT.
iAssert (termT lm2 m2) as "Hm2".
  iApply termT_of_list; rewrite /=; iSplit; eauto.
  iSplit; first by iDestruct "HnB" as "[??]".
  iSplit=> //.
  iApply sub_termT; last by iApply termT_TAEnc; eauto.
  by case: (lm2).
wp_bind (send _); iApply wp_send.
  iModIntro.
  iApply termT_aenc_pub_secG; eauto.
  case: (lm2) => //.
  rewrite /=.
  iModIntro.
  iExists nA, nB, kB; iSplit => //.
wp_pures; wp_bind (recv _); iApply wp_recv; iIntros (m3) "#Hm3".
wp_dec m3; last protocol_failure.
iDestruct (termT_adec_pub_sec with "Hm3 HkB") as (lm3) "/= {Hm3} [#Hm3 #Hprot3]".
wp_untag m3; last protocol_failure.
wp_eq_term e; last protocol_failure; subst m3.
iPoseProof (termT_untag with "Hm3") as "{Hm3} Hm3".
iAssert (⌜lm2 ⊑ lm3⌝)%I as "%lm2_lm3".
  by iDestruct "HnB" as "[_ #Hmin]"; iApply "Hmin".
iPoseProof (guarded_leq with "Hprot3") as "{Hprot3 Hm3} Hprot3"; first eassumption.
clear lm2_lm3 lm3.
wp_pures.
iApply ("Hpost" $! (Some (_, _, _))).
iExists _, _; iSplit => //.
iSplit => //.
iSplit; first by iApply (sub_termT with "HnA"); case: (lm2).
iSplit; first by iDestruct "HnB" as "[HnB _]"; iApply (sub_termT with "HnB"); case: (lm2).
iIntros "#HkA'".
rewrite /lm2.
iPoseProof (pub_enc_keyS' with "Hctx HkA HkA'") as "->".
rewrite decide_True //=.
iDestruct "Hprot3" as "#Hprot3".
iDestruct (tagged_inv_elim' with "Hprot3") as (nA' kA') "[frag1 frag2]".
set sB' := (Session Resp _ _ _).
iPoseProof (term_session_agree with "Hauth frag2") as "%sess".
have [-> ->] : sB' = sB by apply: to_session_included_eq => //=; eauto.
by iSplit=> //.
Qed.

End NSL.
