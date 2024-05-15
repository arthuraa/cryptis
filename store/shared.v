From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib version term cryptis primitives tactics.
From cryptis Require Import role session pk_auth pk_dh.
From cryptis.store Require Import alist db.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Record cst := {
  cst_ts   : loc;
  cst_key  : term;
  cst_name : gname;
  cst_ok   : bool;
}.

#[global]
Instance cst_repr : Repr cst := λ s, (#(cst_ts s), Spec.mkskey (cst_key s))%V.

Record sst := {
  sst_ts  : loc;
  sst_key : term;
  sst_db  : loc;
  sst_ok  : bool;
}.

#[global]
Instance sst_repr : Repr sst :=
  λ s, (#(sst_ts s), Spec.mkskey (sst_key s), #(sst_db s))%V.

Class storeGS Σ := StoreGS {
  storeGS_db : dbGS Σ;
}.

Local Existing Instance storeGS_db.

Definition storeΣ := dbΣ.

Global Instance subG_storeGS Σ : subG storeΣ Σ → storeGS Σ.
Proof. solve_inG. Qed.

Section Defs.

Context `{!cryptisGS Σ, !heapGS Σ, !sessionGS Σ, !storeGS Σ}.
Notation iProp := (iProp Σ).

Local Instance STORE : PK := PK_DH (λ _ _ _ _, True)%I.

Implicit Types (cs : cst).
Implicit Types kI kR kS t : term.
Implicit Types db : gmap term term.
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types v : val.
Implicit Types ok : bool.

Variable N : namespace.

Definition handshake_done kS ok : iProp := ∃ kI kR kS' ph T,
  ⌜kS = Spec.tag (nroot.@"keys".@"sym") kS'⌝ ∗
  ⌜ok = in_honest kI kR T⌝ ∗
  pk_dh_session_weak N (λ _ _ _ _, True)%I Init kI kR kS' ph T.

#[global]
Instance handshake_done_persistent kS ok :
  Persistent (handshake_done kS ok).
Proof. apply _. Qed.

Definition wf_key kS γ : iProp :=
  □ (∀ kt, public (TKey kt kS) -∗ ◇ False) ∗
  □ ∀ kS', ⌜kS = Spec.tag (nroot.@"keys".@"sym") kS'⌝ -∗ ∃ kI kR ph T,
    pk_dh_session_meta N (λ _ _ _ _, True)%I Init kI kR kS' N γ ∗
    pk_dh_session_key N (λ _ _ _ _, True)%I kI kR kS' ph T.

#[global]
Instance wf_key_persistent kS γ : Persistent (wf_key kS γ).
Proof. apply _. Qed.

Lemma handshake_done_session_key kS ok kI kR ph T :
  handshake_done (Spec.tag (nroot.@"keys".@"sym") kS) ok -∗
  pk_dh_session_key N (λ _ _ _ _, True)%I kI kR kS ph T -∗
  ⌜ok = in_honest kI kR T⌝.
Proof.
iIntros "(%kI' & %kR' & %kS' & %ph' & %T' & %e_kS & %e_ok & #weak)".
case/Spec.tag_inj: e_kS => _ <- {kS'}.
iIntros "#key".
by iDestruct (session_weak_session_key with "weak key") as "(<- & <- & <- & <-)".
Qed.

Lemma wf_key_agree kS ok γ γ' :
  handshake_done kS ok -∗
  wf_key kS γ -∗
  wf_key kS γ' -∗
  ⌜γ = γ'⌝.
Proof.
iIntros "(%kI & %kR & %kS' & %ph & %T & -> & %e_ok & #weak)".
iIntros "(_ & #wf1) (_ & #wf2)".
iDestruct ("wf1" with "[//]") as "(%kI1 & %kR1 & %ph1 & %T1 & meta1 & key1)".
iDestruct ("wf2" with "[//]") as "(%kI2 & %kR2 & %ph2 & %T2 & meta2 & key2)".
iDestruct (session_weak_session_key with "weak key1") as "(<- & <- & <- & <-)".
iDestruct (session_weak_session_key with "weak key2") as "(<- & <- & <- & <-)".
by iApply (term_meta_agree with "meta1 meta2").
Qed.

Definition client cs : iProp := ∃ (n : nat),
  handshake_done (cst_key cs) (cst_ok cs) ∗
  (if cst_ok cs then wf_key (cst_key cs) (cst_name cs) else True) ∗
  minted (cst_key cs) ∗
  cst_ts cs ↦ #n ∗
  DB.client_view (cst_name cs) n.

Definition rem_mapsto cs t1 t2 : iProp :=
  DB.mapsto (cst_name cs) t1 t2.

Definition server ss : iProp := ∃ (n : nat) kvs db,
  handshake_done (sst_key ss) (sst_ok ss) ∗
  minted (sst_key ss) ∗
  sst_ts ss ↦ #n ∗
  sst_db ss ↦ kvs ∗
  ⌜AList.is_alist kvs db⌝ ∗
  ([∗ map] t1 ↦ t2 ∈ db, public t1 ∗ public t2) ∗
  (if sst_ok ss then ∃ γ, wf_key (sst_key ss) γ ∗ DB.server_view γ n db
   else True).

Definition init_pred kS (m : term) : iProp := ∃ ok γ,
  handshake_done kS ok ∗
  (if ok then wf_key kS γ else True) ∗
  DB.server_view γ 0 ∅.


Definition store_pred kS m : iProp := ∃ γ (n : nat) t1 t2 ok,
  ⌜m = Spec.of_list [TInt n; t1; t2]⌝ ∗
  handshake_done kS ok ∗
  (if ok then wf_key kS γ else True) ∗
  public t1 ∗
  public t2 ∗
  DB.update_at γ n t1 t2.

Definition ack_store_pred kS m : iProp := ∃ (n : nat),
  ⌜m = TInt n⌝. (* FIXME: Do we need anything else here? *)

Definition load_pred (kS m : term) : iProp := True.

Definition ack_load_pred (kS m : term) : iProp := ∃ (n : nat) ok t1 t2,
  ⌜m = Spec.of_list [TInt n; t1; t2]⌝ ∗
  public t2 ∗
  handshake_done kS ok ∗
  if ok then
    ∃ γ, wf_key kS γ ∗ DB.stored_at γ n t1 t2
  else True.

Definition create_pred kS m : iProp := ∃ γ (n : nat) t1 t2 ok,
  ⌜m = Spec.of_list [TInt n; t1; t2]⌝ ∗
  handshake_done kS ok ∗
  (if ok then wf_key kS γ else True) ∗
  public t1 ∗
  public t2 ∗
  DB.create_at γ n t1 t2.

Definition ack_create_pred kS m : iProp := ∃ (n : nat) t1 t2 (b : bool) ok,
  ⌜m = Spec.of_list [TInt n; t1; t2; TInt (if b then 1 else 0)]⌝ ∗
  handshake_done kS ok ∗
  if ok then
    ∃ γ, wf_key kS γ ∗ if b then DB.free_at γ n t1 else True
  else True.

Definition store_ctx : iProp :=
  enc_pred (N.@"init") init_pred ∗
  enc_pred (N.@"store") store_pred ∗
  enc_pred (N.@"ack_store") ack_store_pred ∗
  enc_pred (N.@"load") load_pred ∗
  enc_pred (N.@"ack_load") ack_load_pred ∗
  enc_pred (N.@"create") create_pred ∗
  enc_pred (N.@"ack_create") ack_create_pred ∗
  pk_dh_ctx N (λ _ _ _ _, True)%I.

Lemma handshake_done_agree kS γ ok1 ok2 :
  wf_key kS γ -∗
  handshake_done kS ok1 -∗
  handshake_done kS ok2 -∗
  ⌜ok1 = ok2⌝.
Proof.
iIntros "(_ & #impl)".
iIntros "(%kI1 & %kR1 & %kS1 & %ph1 & %T1 & -> & -> & #sess1)".
iIntros "(%kI2 & %kR2 & %kS2 & %ph2 & %T2 & %e_kS & -> & #sess2)".
case/Spec.tag_inj: e_kS => _ <- {kS2}.
iPoseProof ("impl" with "[//]") as "(%kI & %kR & %ph' & %T' & #meta & #key)" => //.
iPoseProof (session_weak_session_key with "sess1 key") as "(<- & <- & <- & <-)".
iPoseProof (session_weak_session_key with "sess2 key") as "(<- & <- & <- & <-)".
by eauto.
Qed.

Lemma initE kS t :
  store_ctx -∗
  public (TEnc kS (Spec.tag (N.@"init") t)) -∗
  public (TKey Enc kS) ∨
  ▷ ∃ ok γ, handshake_done kS ok ∗
            (if ok then wf_key kS γ else True) ∗
            DB.server_view γ 0 ∅.
Proof.
iIntros "(#initP & _) #p_t".
iDestruct (public_TEncE with "[//] [//]") as "[[??]|#tP]"; first by eauto.
iRight. by iDestruct "tP" as "(#init & _ & _)".
Qed.

Lemma store_predE kS ok n t1 t2 :
  handshake_done kS ok -∗
  (if ok then ∃ γ, wf_key kS γ else True) -∗
  store_ctx -∗
  public (TEnc kS (Spec.tag (N.@"store")
                  (Spec.of_list [TInt n; t1; t2]))) -∗
  ▷ (public t1 ∗ public t2 ∗
     if ok then ∃ γ, wf_key kS γ ∗ DB.update_at γ n t1 t2 else True).
Proof.
iIntros "#key #wf #(_ & #storeP & _) #p_m".
iPoseProof (public_TEncE with "p_m [//]") as "{p_m} p_m".
rewrite public_of_list /=. iDestruct "p_m" as "[p_m|p_m]".
- iDestruct "p_m" as "(p_k & p_m & ? & ? & ?)".
  do 2!iSplit => //. case: ok => //.
  iDestruct "wf" as "(%γ & #contra & _)".
  iDestruct ("contra" with "p_k") as ">[]".
- iDestruct "p_m" as "(#(%γ & %n' & %t1' & %t2' & %ok' & mP) & _ & _)".
  iModIntro. iDestruct "mP" as "(%e & done & wf' & p_t1 & p_t2 & update)".
  case/Spec.of_list_inj: e => en <- <-.
  have -> : n' = n by lia.
  do 2!iSplitL => //.
  case: ok => //.
  iDestruct "wf" as "(%γ' & wf)".
  iPoseProof (handshake_done_agree with "wf key done") as "<-".
  iExists γ. eauto.
Qed.

Lemma ack_loadE kS ok n γ t1 t2 t2' :
  handshake_done kS ok -∗
  (if ok then wf_key kS γ else True) -∗
  DB.client_view γ n -∗
  DB.mapsto γ t1 t2 -∗
  store_ctx -∗
  public (TEnc kS (Spec.tag (N.@"ack_load")
         (Spec.of_list [TInt n; t1; t2']))) -∗
  ▷ (public t2' ∗
     if ok then ⌜t2' = t2⌝ else True%I).
Proof.
iIntros "#key #wf client mapsto #(_ & _ & _ & _ & ? & _) #pub".
iDestruct (public_TEncE with "pub [//]") as "{pub} [pub|pub]".
- iDestruct "pub" as "[pub_k pub_t2]".
  rewrite public_of_list /=.
  iDestruct "pub_t2" as "(_ & _ & pub_t2 & _)".
  iSplit => //.
  case: ok => //.
  iDestruct "wf" as "(#wf & _)".
  iDestruct ("wf" with "pub_k") as ">[]".
- iDestruct "pub" as "(#pub & _ & _)". iModIntro.
  iDestruct "pub" as "(%n' & %ok' & %t1' & %t2'' & %E & ? & key' & stored)".
  case/Spec.of_list_inj: E => en <- <-.
  have <- : n = n' by lia.
  iSplit => //.
  case: ok => //.
  iPoseProof (handshake_done_agree with "wf key key'") as "<-".
  iDestruct "stored" as "(%γ' & wf' & stored)".
  iPoseProof (wf_key_agree with "key wf wf'") as "->".
  iApply (DB.load_client with "client mapsto stored").
Qed.

End Defs.

Arguments storeGS Σ : clear implicits.
