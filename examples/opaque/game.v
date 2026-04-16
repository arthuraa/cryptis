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

Definition unguessable_option : val :=
  λ: "x" "c",
    bind: "x'" := "x" in
      assert: (~ eq_term "x'" (recv "c")).

Lemma wp_unguessable_option (x : option term) (c : val) ϕ e :
channel c -∗
SK_priv x -∗
WP e {{ v , ϕ v }} -∗
WP unguessable_option (repr x) c ;; e {{ v, ϕ v }}.
Proof.
iIntros "#? Hprivx Hpost".
wp_lam.
wp_pures.
destruct x as [x|]; wp_pures => //.
wp_apply wp_assert.
wp_apply wp_recv => //.
iIntros "%guess #pubguess".
wp_bind (eq_term _ _).
wp_eq_term H.
rewrite H.
simpl.
iSpecialize ("Hprivx" with "pubguess").
wp_pures.
by iDestruct "Hprivx" as "%Hprivx".
wp_pures.
iModIntro.
iSplit => //.
iNext.
by wp_pures.
Qed.

Definition neq_options : val :=
λ: "x1" "x2",
bind: "x1'" := "x1" in
bind: "x2'" := "x2" in
assert: (~ eq_term "x1'" "x2'").

Lemma wp_neq_options (x1 x2 : option term) ϕ e :
  SK_fresh x2 match x1 with
                None => ∅
              | Some x1' => {[x1']}
              end -∗
WP e {{ v , ϕ v }} -∗
WP neq_options (repr x1) (repr x2) ;; e {{ v, ϕ v }}.
iIntros "Hfresh Hpost".
wp_lam.
destruct x1 as [x1|]; wp_pures => //.
destruct x2 as [x2|]; wp_pures => //.
wp_apply wp_assert.
iDestruct "Hfresh" as "%Hfresh".
rewrite elem_of_singleton in Hfresh.
wp_bind (eq_term _ _).
wp_eq_term H.
by destruct Hfresh.
wp_pures.
iModIntro.
iSplitR => //.
iNext.
by wp_pures.
Qed.

Definition game : val :=
λ: <>,
let: "c" := init_network #() in
let: "uid" := mk_nonce #() in
let: "pw" := mk_nonce #() in
let: "db" := AList.new #() in
AList.insert "db" "uid" (Server.make_file "pw") ;;
let: "SK1s" := Server.session "db" "c" ||| Client.session "uid" "c" "pw" in
assert: (~ eq_term "pw" (recv "c")) ;;
unguessable_option (Fst "SK1s") "c" ;;
unguessable_option (Snd "SK1s") "c" ;;
let: "SK2s" := Server.session "db" "c" ||| Client.session "uid" "c" "pw" in
unguessable_option (Fst "SK2s") "c" ;;
unguessable_option (Snd "SK2s") "c" ;;
neq_options (Fst "SK1s") (Fst "SK2s") ;;
neq_options (Snd "SK1s") (Snd "SK2s") ;;
#().

Lemma wp_game :
cryptis_ctx -∗
hash_pred_token ⊤ -∗
seal_pred_token SENC ⊤ -∗
WP game #() {{ (fun _ => True) }}.
Proof.
iIntros "#? h_pred_tok s_pred_tok".
iMod (opaque_alloc with "h_pred_tok s_pred_tok") as
"[(#? & #? & #? & #? & #? & #? & #?) _]" => //.
wp_lam.
wp_apply wp_init_network => //.
iIntros "%c #Hchannel".
wp_pures.
wp_apply (wp_mk_nonce (fun _ => True)%I (fun _ => False)%I) => //.
iIntros "%uid %Hnonceuid #Hminuid #Hpubuid #Hdhuid _ _ _".
iAssert (public uid) as "Hpubuid'".
by iApply "Hpubuid".
iClear "Hpubuid".
wp_pures.
wp_apply (wp_mk_nonce (fun _ => False)%I (fun _ => False)%I) => //.
iIntros "%pw %Hnoncepw #Hminpw #Hprivpw #Hdhpw _ _ _".
wp_pures.
wp_bind (AList.new #()).
iApply AList.wp_empty => //.
iNext.
iIntros "%db Halist".
wp_pures.
wp_apply (wp_make_file pw).
do !iSplit => //.
iIntros "%file #Hopaquefile" => /=.
wp_bind (AList.insert db uid file).
iApply (AList.wp_insert with "Halist").
iNext.
iIntros "Halist".
wp_pures.
wp_apply (wp_par (fun x => (SK_result' x ∅ ∗ AList.is_alist db (<[uid:=file]> ∅))%I)
                 (fun x => (SK_result' x ∅)) with "[Halist]").
iApply (wp_server_session db c (<[uid:=file]> ∅) ∅  with "[Halist]") => //.
do !iSplit => //.
iApply big_sepM_insert => //.
do !iSplit => //.
by iIntros "% %".
iNext.
iIntros "%x".
iIntros "(? & Halist)".
iSplitR "Halist" => //.
by iApply SK_result_eq.
iApply (wp_client_session uid pw c ∅).
do !iSplit => //.
by iIntros "% %".
iNext.
iIntros "%x".
iIntros "?".
by iApply SK_result_eq.
iIntros "%SKs1' %SKc1'
    [[(%SKs1 & -> & HprivSKs1 & _ & HminSKs1) Halist]
    (%SKc1 & -> & HprivSKc1 & _ & HminSKc1)]".
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
wp_apply (wp_unguessable_option SKs1 c with "Hchannel HprivSKs1").
wp_pures.
wp_apply (wp_unguessable_option SKc1 c with "Hchannel HprivSKc1").
wp_pures.
Check wp_par.
Check (fun x => match SKs1 with
               None => True
             | Some SKs1' => SK_result' x {[SKs1']}
             end ∗ AList.is_alist db (<[uid:=file]> ∅))%I.
wp_apply (wp_par
          (fun x => SK_result' x match SKs1 with
                                None => ∅
                              | Some x' => {[x']}
                              end
                            ∗ AList.is_alist db (<[uid:=file]> ∅))%I
          (fun x => SK_result' x match SKc1 with
                                None => ∅
                              | Some x' => {[x']}
                              end)%I with "[Halist HminSKs1] [HminSKc1]").
iApply (wp_server_session db c (<[uid:=file]> ∅) match SKs1 with
                                None => ∅
                              | Some x' => {[x']}
                              end  with "[Halist HminSKs1]") => //.
do !iSplit => //.
iApply big_sepM_insert => //.
by do !iSplit => //.
iIntros "%".
destruct SKs1 as [SKs1|].
rewrite elem_of_singleton.
by iIntros "->".
by iIntros "%".
iNext.
iIntros "%x".
iIntros "(? & Halist)".
iSplitR "Halist" => //.
by iApply SK_result_eq.
iApply (wp_client_session uid pw c match SKc1 with
                                     None => ∅
                                   | Some x' => {[x']}
                                   end with "[HminSKc1]").
do !iSplit => //.
iIntros "%".
destruct SKc1 as [SKc1|].
rewrite elem_of_singleton.
by iIntros "->".
by iIntros "%".
iNext.
iIntros "%x ?".
by iApply SK_result_eq.
iIntros "%SKs2' %SKc2'
    [[(%SKs2 & -> & HprivSKs2 & HfreshSKs2 & _) _]
    (%SKc2 & -> & HprivSKc2 & HfreshSKc2 & _)]".
iNext.
wp_pures.
wp_apply (wp_unguessable_option SKs2 with "Hchannel HprivSKs2").
wp_pures.
wp_apply (wp_unguessable_option SKc2 with "Hchannel HprivSKc2").
wp_pures.
wp_apply (wp_neq_options SKs1 SKs2 with "HfreshSKs2").
wp_pures.
wp_apply (wp_neq_options SKc1 SKc2 with "HfreshSKc2").
by wp_pures.
Qed.

End Game.
