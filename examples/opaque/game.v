From mathcomp Require Import ssreflect.
From iris.heap_lang Require Import proofmode.
From iris.heap_lang.lib Require Import assert.

From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import par lock ticket_lock.
From cryptis.examples Require Import alist.

From cryptis.examples.opaque Require Import impl server_proofs client_proofs shared.
From cryptis Require Import lib term cryptis primitives tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Game.

Context `{!cryptisGS Σ, !heapGS Σ, !spawnG Σ}.
Notation iProp := (iProp Σ).

Definition game : val :=
λ: <>,
let: "c" := init_network #() in
let: "uid" := mk_nonce #() in
let: "pw" := mk_nonce #() in
let: "db" := AList.new #() in
AList.insert "db" "uid" (Server.make_file "pw") ;;
let: "SKs" := Server.session "db" "c" ||| Client.session "uid" "c" "pw" in
assert: (~ eq_term "pw" (recv "c")) ;;
(bind: "SK" := (Fst "SKs") in
   assert: (~ eq_term "SK" (recv "c"));;
           NONE) ;;
(bind: "SK" := (Snd "SKs") in
   assert: (~ eq_term "SK" (recv "c"));;
           NONE).

Lemma wp_game :
{{{ cryptis_ctx
    ∗ hash_pred_token ⊤
    ∗ seal_pred_token SENC ⊤}}}
game #()
{{{ x , RET x ; True }}}.
Proof.
iIntros "%ϕ (#? & h_pred_tok & s_pred_tok) Hhl".
iMod (opaque_alloc with "h_pred_tok s_pred_tok") as
  "[(#? & #? & #? & #? & #? & #? & #?) _]" => //.
wp_lam.
wp_apply wp_init_network => //.
iIntros "%c #Hchannel".
wp_pures.
wp_apply (wp_mk_nonce (fun _ => True)%I (fun _ => False)%I) => //.
iIntros "%uid %Hnonceuid #Hminuid #Hpubuid #Hdhuid _ _ Htermtokenuid".
iAssert (public uid) as "Hpubuid'".
by iApply "Hpubuid".
iClear "Hpubuid".
wp_pures.
wp_apply (wp_mk_nonce (fun _ => False)%I (fun _ => False)%I) => //.
iIntros "%pw %Hnoncepw #Hminpw #Hprivpw #Hdhpw _ _ Htermtokenpw".
wp_pures.
wp_bind (AList.new #()).
iApply AList.wp_empty => //.
iNext.
iIntros "%db Halist".
wp_pures.
wp_apply (wp_make_file pw).
do !iSplit => //.
iIntros "%file Hopaquefile" => /=.
wp_bind (AList.insert db uid file).
iApply (AList.wp_insert with "Halist").
iNext.
iIntros "Halist".
wp_pures.
wp_apply (wp_par SK_priv' SK_priv' with "[Halist Hopaquefile]").
iApply (wp_server_session db c (<[uid:=file]> ∅)  with "[Halist Hopaquefile]") => //.
do !iSplit => //.
iApply big_sepM_insert => //.
do !iSplit => //.
iNext.
iIntros "%x".
by iApply SK_priv_eq.
iApply (wp_client_session uid pw c).
do !iSplit => //.
iNext.
iIntros "%_".
by iApply SK_priv_eq.
iIntros "%SK1 %SK2 [(%SK1' & -> & HprivSK1) (%SK2' & -> & HprivSK2)]".
iNext.
wp_pures.
wp_apply wp_assert.
wp_apply wp_recv => //.
iIntros "%attack #Hpubattack".
wp_bind (eq_term _ _).
wp_eq_term H.
rewrite H.
iDestruct "Hprivpw" as "[Hprivpw _]".
iDestruct ("Hprivpw" with "Hpubattack") as "Hcontra".
all: wp_pures.
by iDestruct "Hcontra" as "%Hcontra".
clear H.
iModIntro.
iSplit => //.
iNext.
wp_pures.
wp_bind (bind: _ := _ in _)%E.
iApply (wp_wand _ _ _ (λ v, ⌜v = InjLV #() ⌝)%I with "[HprivSK1]").
destruct SK1'; wp_pures => //.
wp_apply wp_assert.
wp_apply wp_recv => //.
iIntros "%guess #pubguess".
wp_bind (eq_term _ _).
wp_eq_term H.
rewrite H.
iSpecialize ("HprivSK1" with "pubguess").
wp_pures.
by iDestruct "HprivSK1" as "%HprivSK1".
wp_pures.
iModIntro.
iSplit => //.
iNext.
by wp_pures.
iIntros "%_ ->".
wp_pures.
wp_bind (bind: _ := _ in _)%E.
iApply (wp_wand _ _ _ (λ v, ⌜v = InjLV #() ⌝)%I with "[HprivSK2]").
destruct SK2'; wp_pures => //.
wp_apply wp_assert.
wp_apply wp_recv => //.
iIntros "%guess #pubguess".
wp_bind (eq_term _ _).
wp_eq_term H.
rewrite H.
iSpecialize ("HprivSK2" with "pubguess").
wp_pures.
by iDestruct "HprivSK2" as "%HprivSK2".
wp_pures.
iModIntro.
iSplit => //.
iNext.
by wp_pures.
iIntros "%_ ->".
by iApply "Hhl".
Qed.

End Game.
