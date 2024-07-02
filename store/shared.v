From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces coGset.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib version term cryptis primitives tactics.
From cryptis Require Import role dh_auth.
From cryptis.store Require Import alist db.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Record cst := {
  cst_si   :> sess_info;
  cst_ts   :  loc;
  cst_name :  gname;
}.

#[global]
Instance cst_repr : Repr cst :=
  λ s, (#(cst_ts s), Spec.mkskey (si_key s))%V.

Record sst := {
  sst_si  :> sess_info;
  sst_ts  : loc;
  sst_db  : loc;
}.

#[global]
Instance sst_repr : Repr sst :=
  λ s, (#(sst_ts s), Spec.mkskey (si_key s), #(sst_db s))%V.

Class storeGS Σ := StoreGS {
  storeGS_db : dbGS Σ;
}.

Local Existing Instance storeGS_db.

Definition storeΣ := dbΣ.

Global Instance subG_storeGS Σ : subG storeΣ Σ → storeGS Σ.
Proof. solve_inG. Qed.

Section Defs.

Context `{!cryptisGS Σ, !heapGS Σ, !storeGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (cs : cst) (ss : sst).
Implicit Types kI kR kS t : term.
Implicit Types db : gmap term term.
Implicit Types n : nat.
Implicit Types b : bool.
Implicit Types γ : gname.
Implicit Types v : val.
Implicit Types ok : bool.
Implicit Types si : sess_info.

Variable N : namespace.

Definition client cs : iProp := ∃ (n : nat),
  session cs Init (cst_name cs) ∗
  □ (∀ kt, public (TKey kt (si_key cs)) ↔ ▷ ⌜¬ session_ok cs⌝) ∗
  minted (si_key cs) ∗
  cst_ts cs ↦ #n ∗
  DB.client_view (cst_name cs) n.

Definition rem_mapsto cs t1 t2 : iProp :=
  DB.mapsto (cst_name cs) t1 t2.

Definition rem_free_at cs T : iProp :=
  DB.free_at (cst_name cs) T.

Lemma rem_free_at_diff cs T1 T2 :
  T1 ⊆ T2 →
  rem_free_at cs T2 ⊣⊢ rem_free_at cs T1 ∗ rem_free_at cs (T2 ∖ T1).
Proof. exact: DB.free_at_diff. Qed.

Definition server ss : iProp := ∃ γ (n : nat) kvs db,
  session ss Resp γ ∗
  □ (∀ kt, public (TKey kt (si_key ss)) ↔ ▷ ⌜¬ session_ok ss⌝) ∗
  minted (si_key ss) ∗
  sst_ts ss ↦ #n ∗
  sst_db ss ↦ kvs ∗
  ⌜AList.is_alist kvs (repr <$> db)⌝ ∗
  ([∗ map] t1 ↦ t2 ∈ db, public t1 ∗ public t2) ∗
  (⌜session_ok ss⌝ -∗ ∃ γ', session ss Init γ' ∗ DB.server_view γ' n db).

Definition init_pred kS (m : term) : iProp := ∃ si γ,
  ⌜si_key si = kS⌝ ∗
  session si Init γ ∗
  DB.server_view γ 0 ∅.

Definition store_pred kS m : iProp := ∃ (n : nat) t1 t2 si γ,
  ⌜m = Spec.of_list [TInt n; t1; t2]⌝ ∗
  ⌜si_key si = kS⌝ ∗
  session si Init γ ∗
  public t1 ∗
  public t2 ∗
  DB.update_at γ n t1 t2.

Definition ack_store_pred kS m : iProp := ∃ (n : nat),
  ⌜m = TInt n⌝. (* FIXME: Do we need anything else here? *)

Definition load_pred (kS m : term) : iProp := True.

Definition ack_load_pred (kS m : term) : iProp := ∃ n t1 t2 si γ,
  ⌜m = Spec.of_list [TInt n; t1; t2]⌝ ∗
  ⌜si_key si = kS⌝ ∗
  public t2 ∗
  session si Resp γ ∗
  (⌜session_ok si⌝ -∗ ∃ γ', session si Init γ' ∗ DB.stored_at γ' n t1 t2).

Definition create_pred kS m : iProp := ∃ n t1 t2 si γ,
  ⌜m = Spec.of_list [TInt n; t1; t2]⌝ ∗
  ⌜si_key si = kS⌝ ∗
  session si Init γ ∗
  public t1 ∗
  public t2 ∗
  DB.create_at γ n t1 t2.

Definition ack_create_pred kS (m : term) : iProp := True.

Definition store_ctx : iProp :=
  enc_pred (N.@"init") init_pred ∗
  enc_pred (N.@"store") store_pred ∗
  enc_pred (N.@"ack_store") ack_store_pred ∗
  enc_pred (N.@"load") load_pred ∗
  enc_pred (N.@"ack_load") ack_load_pred ∗
  enc_pred (N.@"create") create_pred ∗
  enc_pred (N.@"ack_create") ack_create_pred ∗
  dh_auth_ctx (N.@"auth").

Lemma store_ctx_alloc E :
  ↑N ⊆ E →
  enc_pred_token E ==∗
  store_ctx ∗ enc_pred_token (E ∖ ↑N).
Proof.
iIntros "%sub token".
rewrite (enc_pred_token_difference (↑N)) => //.
iDestruct "token" as "[token ?]". iFrame.
iMod (enc_pred_set (N.@"init") init_pred with "token")
  as "[#init token]"; try solve_ndisj.
iMod (enc_pred_set (N.@"store") store_pred with "token")
  as "[#store token]"; try solve_ndisj.
iMod (enc_pred_set (N.@"ack_store") ack_store_pred with "token")
  as "[#ack_store token]"; try solve_ndisj.
iMod (enc_pred_set (N.@"load") load_pred with "token")
  as "[#load token]"; try solve_ndisj.
iMod (enc_pred_set (N.@"ack_load") ack_load_pred with "token")
  as "[#ack_load token]"; try solve_ndisj.
iMod (enc_pred_set (N.@"create") create_pred with "token")
  as "[#create token]"; try solve_ndisj.
iMod (enc_pred_set (N.@"ack_create") ack_create_pred with "token")
  as "[#ack_create token]"; try solve_ndisj.
iMod (dh_auth_ctx_alloc (N.@"auth") with "token")
  as "#dh_auth"; try solve_ndisj.
iModIntro. do !iSplit => //.
Qed.

Lemma initE si γ t :
  store_ctx -∗
  session si Resp γ -∗
  □ (∀ kt, public (TKey kt (si_key si)) ↔ ▷ ⌜¬ session_ok si⌝) -∗
  public (TEnc (si_key si) (Spec.tag (N.@"init") t)) -∗
  ▷ (⌜session_ok si⌝ -∗ ∃ γ, session si Init γ ∗ DB.server_view γ 0 ∅).
Proof.
iIntros "(#initP & _) #sessR #kS #p_t".
iDestruct (public_TEncE with "[//] [//]") as "[[p_kS ?]|#tP]".
{ iPoseProof ("kS" with "p_kS") as ">%comp".
  iIntros "!> %". tauto. }
iDestruct "tP" as "(#init & _ & _)".
iModIntro.
iDestruct "init" as "(%si' & %γ' & %e_kS & sessI & #view)".
iIntros "%ok".
iPoseProof (session_agree with "sessI sessR") as "->" => //.
by eauto.
Qed.

Lemma store_predE si γ n t1 t2 :
  store_ctx -∗
  session si Resp γ -∗
  □ (∀ kt, public (TKey kt (si_key si)) ↔ ▷ ⌜¬ session_ok si⌝) -∗
  □ (⌜session_ok si⌝ -∗ ∃ γ, session si Init γ) -∗
  public (TEnc (si_key si) (Spec.tag (N.@"store")
                              (Spec.of_list [TInt n; t1; t2]))) -∗
  ▷ (public t1 ∗ public t2 ∗
     (⌜session_ok si⌝ -∗ ∃ γ, session si Init γ ∗ DB.update_at γ n t1 t2)).
Proof.
iIntros "#(_ & #storeP & _) #sessR #key #sessI #p_m".
iPoseProof (public_TEncE with "p_m [//]") as "{p_m} p_m".
rewrite public_of_list /=. iDestruct "p_m" as "[p_m|p_m]".
- iDestruct "p_m" as "(p_k & p_m & ? & ? & ?)".
  do 2!iSplit => //.
  iPoseProof ("key" with "p_k") as ">%".
  iIntros "!> %". tauto.
- iModIntro.
  iDestruct "p_m" as "(#(%n' & %t1' & %t2' & %si' & %γ' & mP) & _ & _)".
  iDestruct "mP" as "(%e & %e_key & sessI' & p_t1 & p_t2 & update)".
  case/Spec.of_list_inj: e => en <- <-.
  have -> : n' = n by lia.
  do 2!iSplitL => //.
  iIntros "%ok".
  iDestruct ("sessI" with "[//]") as "{sessI} [%γ'' sessI]" => //.
  iPoseProof (session_agree_name with "sessI' sessI") as "(-> & <-)" => //.
  iExists γ'.
  by eauto.
Qed.

Lemma ack_loadE si γ n t1 t2 t2' :
  store_ctx -∗
  session si Init γ -∗
  □ (∀ kt, public (TKey kt (si_key si)) ↔ ▷ ⌜¬ session_ok si⌝) -∗
  DB.client_view γ n -∗
  DB.mapsto γ t1 t2 -∗
  public (TEnc (si_key si) (Spec.tag (N.@"ack_load")
         (Spec.of_list [TInt n; t1; t2']))) -∗
  ▷ (public t2' ∗ ⌜session_ok si → t2' = t2⌝).
Proof.
iIntros "#(_ & _ & _ & _ & ? & _) #sessI #key client mapsto #pub".
iDestruct (public_TEncE with "pub [//]") as "{pub} [pub|pub]".
- iDestruct "pub" as "[pub_k pub_t2]".
  rewrite public_of_list /=.
  iDestruct "pub_t2" as "(_ & _ & pub_t2 & _)".
  iSplit => //.
  iPoseProof ("key" with "pub_k") as ">%".
  by iIntros "%".
- iDestruct "pub" as "(#pub & _ & _)". iModIntro.
  iDestruct "pub" as "(%n' & %t1' & %t2'' & %si' & %γ' &
                       %e & %e_kS & ? & #sessR & stored)".
  case/Spec.of_list_inj: e => en <- <-.
  have <- : n = n' by lia.
  iSplit => //.
  iIntros "%ok".
  iPoseProof (session_agree with "sessR sessI") as "->" => //.
  iDestruct ("stored" with "[//]") as "{stored} (%γ'' & sessI' & stored)".
  iPoseProof (session_agree_name with "sessI' sessI") as "(_ & ->)" => //.
  iApply (DB.load_client with "client mapsto stored").
Qed.

End Defs.

Arguments storeGS Σ : clear implicits.
