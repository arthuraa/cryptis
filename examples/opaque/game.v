From mathcomp Require Import ssreflect.
From iris.heap_lang Require Import proofmode.
From iris.heap_lang.lib Require Import assert.

From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import lock ticket_lock.
From cryptis.examples Require Import alist.

From cryptis.examples.opaque Require Import impl server_proofs client_proofs shared.
From cryptis Require Import lib term cryptis primitives tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Game.

Context `{!cryptisGS Σ, !heapGS Σ}.
Notation iProp := (iProp Σ).

Definition game : val :=
λ: <>,
let: "c" := init_network #() in
let: "uid" := mk_nonce #() in
let: "pw" := mk_nonce #() in
let: "db" := AList.new #() in
AList.insert "db" "uid" (Server.make_file "pw") ;;
Fork (Server.session "db" "c");;
Client.session "uid" "c" "pw";;
assert: (~ eq_term "pw" (recv "c")).

Lemma wp_game :
{{{ cryptis_ctx
    ∗ hash_pred_token ⊤
    ∗ seal_pred_token SENC ⊤}}}
game #()
{{{ x , RET x ; True }}}.
Proof.
iIntros "%ϕ (#Hcryptis & h_pred_tok & s_pred_tok) Hhl".
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
wp_apply (wp_fork with "[Halist Hopaquefile]").
iApply (wp_server_session db c (<[uid:=file]> ∅)  with "[Halist Hopaquefile]") => //.
do !iSplit => //.
iApply big_sepM_insert => //.
do !iSplit => //. auto.
wp_pures.
wp_bind (Client.session uid c pw).
iApply (wp_client_session uid pw c).
do !iSplit => //.
iNext.
iIntros "%_ _".
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
iModIntro.
iSplit => //.
by iApply "Hhl".
Qed.

End Game.
