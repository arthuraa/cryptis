From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl namespace_map frac.
From iris.base_logic.lib Require Import auth.
From iris.heap_lang Require Import notation proofmode.
From crypto Require Import lib guarded term crypto primitives tactics session.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section NSL.

Context `{!cryptoG Σ, !heapG Σ}.
Notation iProp := (iProp Σ).

Implicit Types t : term.
Implicit Types s : session_view.
Implicit Types l : level.
Implicit Types rl : role.

Class nslG := {
  in_nsl_sessG :> sessionG Σ;
  in_nsl_honestG :> inG Σ (authR (prodUR (gsetUR term) (gsetUR term)));
  nsl_sess_name : gname;
  nsl_honest_name : gname;
}.

Context `{!nslG}.

Global Instance nsl_honest_authG : authG Σ (prodUR (gsetUR term) (gsetUR term)).
Proof. constructor; apply _. Qed.

Definition nsl_honest_proj rl : gset term * gset term → gset term :=
  if rl is Init then fst else snd.

Definition nsl_res_of_key rl k : gset term * gset term :=
  if rl is Init then ({[k]}, ∅) else (∅, {[k]}).

Lemma nsl_res_of_key_included rl k Ks :
  nsl_res_of_key rl k ≼ Ks ↔
  k ∈ nsl_honest_proj rl Ks.
Proof.
case: rl Ks=> [] [K1 K2] /=;
rewrite pair_included !gset_included;
split; intuition set_solver.
Qed.

Definition nsl_key rl (k : term) : iProp :=
  auth_own nsl_honest_name (nsl_res_of_key rl k).

Global Instance nsl_key_persistent rl k :
  Persistent (nsl_key rl k).
Proof. case: rl; apply _. Qed.

Definition msg1_pred (kB : term) m1 : iProp :=
  ∃ nA kA, ⌜m1 = Spec.of_list [nA; TKey Enc kA]⌝ ∧
           stermT Sec nA ∧ nsl_key Init kA.

Global Instance msg1_pred_persistent kB m1 : Persistent (msg1_pred kB m1).
Proof. apply _. Qed.

Definition msg2_pred kA m2 : iProp :=
  ∃ nA nB kB,
    ⌜m2 = Spec.of_list [nA; nB; TKey Enc kB]⌝ ∧
    stermT Sec nA ∧
    stermT Sec nB ∧
    session nsl_sess_name Resp kA kB nA nB.

Global Instance msg2_pred_persistent kB m2 : Persistent (msg2_pred kB m2).
Proof.
case: m2; try by move=> *; apply _.
Qed.

Definition msg3_pred kB nB : iProp :=
  □ ∀ nA kA,
    session nsl_sess_name Resp kA kB nA nB -∗
    session nsl_sess_name Init kA kB nA nB.

Global Instance msg3_pred_persistent kB nB : Persistent (msg3_pred kB nB).
Proof. apply _. Qed.

Definition nsl_key_inv rl k : iProp :=
  termT Pub (TKey Enc k) ∗
  stermT Sec (TKey Dec k) ∗
  match rl with
  | Init => tkey_predT "m2" (msg2_pred k) k
  | Resp => tkey_predT "m1" (msg1_pred k) k ∗
            tkey_predT "m3" (msg3_pred k) k
  end.
Arguments nsl_key_inv : simpl never.

Global Instance nsl_key_inv_persistent rl k :
  Persistent (nsl_key_inv rl k).
Proof. rewrite /nsl_key_inv; case: rl; apply _. Qed.

Definition nsl_keys_inv Ks : iProp := (
  [∗ list] rl ∈ [Init; Resp],
  [∗ set]  k  ∈ nsl_honest_proj rl Ks,
    nsl_key_inv rl k
)%I.

Lemma nsl_keys_inv_elim rl k Ks :
  k ∈ nsl_honest_proj rl Ks →
  nsl_keys_inv Ks -∗
  nsl_key_inv rl k.
Proof.
case: rl => [] /= k_Ks; iIntros "inv"; rewrite /nsl_keys_inv /=.
- iDestruct "inv" as "[inv _]".
  by rewrite big_sepS_forall; iApply "inv".
- iDestruct "inv" as "(_ & inv & _)".
  by rewrite big_sepS_forall; iApply "inv".
Qed.

Variable nsl_sess_inv : role → term → term → term → term → iProp.

Definition nsl_inv : iProp :=
  session_inv nsl_sess_name (cryptoN.@"nsl") nsl_sess_inv.

Definition nsl_ctx : iProp :=
  session_ctx nsl_sess_name (cryptoN.@"nsl") nsl_sess_inv ∧
  auth_ctx nsl_honest_name (cryptoN.@"nsl") id nsl_keys_inv.

Lemma nsl_key_inv_pub rl k : nsl_key_inv rl k -∗ termT Pub (TKey Enc k).
Proof. by iDestruct 1 as "[??]". Qed.

Lemma nsl_key_elim E rl k :
  ↑cryptoN.@"nsl" ⊆ E →
  nsl_ctx -∗
  nsl_key rl k ={E}=∗
  ▷ nsl_key_inv rl k.
Proof.
iIntros (?) "[_ #ctx] #key".
iMod (auth_acc id nsl_keys_inv with "[ctx key]") as "inv"; eauto.
iDestruct "inv" as (Ks) "(%k_K & #inv & close)".
iMod ("close" $! Ks with "[]") as "_"; first by iSplit; eauto.
move: k_K; rewrite nsl_res_of_key_included /= => k_K.
by iIntros "!> !>"; iApply nsl_keys_inv_elim; eauto.
Qed.

Lemma nsl_key_elimG `{Decision G} E rl k :
  ↑cryptoN.@"nsl" ⊆ E →
  nsl_ctx -∗
  guarded G (nsl_key rl k) ={E}=∗
  ▷ guarded G (nsl_key_inv rl k).
Proof.
iIntros (?) "ctx key_k"; rewrite /guarded; case: decide => //= _.
by iApply (nsl_key_elim with "ctx key_k").
Qed.

Variable send recv gen : val.

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None).

Definition initiator (skA pkA pkB nA : val) : val := λ: <>,
  bind: "m1"   := tenc "m1" pkB (term_of_list [nA; pkA]) in
  send "m1";;
  bind: "m2"   := tdec "m2" skA (recv #()) in
  bind: "m2"   := list_of_term "m2" in
  bind: "nA'"  := "m2" !! #0 in
  bind: "nB"   := "m2" !! #1 in
  bind: "pkB'" := "m2" !! #2 in
  if: eq_term "nA'" nA && eq_term "pkB'" pkB then
    bind: "m3" := tenc "m3" pkB "nB" in
    send "m3";;
    SOME "nB"
  else NONE.

Definition responder (skB pkB : val) : val := λ: <>,
  bind: "m1" := tdec "m1" skB (recv #()) in
  bind: "m1" := list_of_term "m1" in
  bind: "nA" := "m1" !! #0 in
  bind: "pkA" := "m1" !! #1 in
  bind: "kt" := is_key "pkA" in
  if: "kt" = repr Enc then
    let: "nB" := gen #() in
    bind: "m2" := tenc "m2" "pkA" (term_of_list ["nA"; "nB"; pkB]) in
    send "m2";;
    bind: "m3" := tdec "m3" skB (recv #()) in
    if: eq_term "m3" "nB" then SOME ("pkA", "nA", "nB") else NONE
  else NONE.

Implicit Types Ψ : val → iProp.

Hypothesis wp_send : forall E t Ψ,
  ▷ termT Pub t -∗
  Ψ #() -∗
  WP send t @ E {{ Ψ }}.

Hypothesis wp_recv : forall E Ψ,
  (∀ t, termT Pub t -∗ Ψ t) -∗
  WP recv #() @ E {{ Ψ }}.

Hypothesis wp_gen : forall E l kA kB nA Ψ,
  (∀ nB,
      crypto_meta_token nB (↑cryptoN.@"nsl") -∗
      stermT l nB -∗
      guarded (l = Sec) (nsl_sess_inv Resp kA kB nA nB) -∗
      Ψ nB) -∗
  WP gen #() @ E {{ Ψ }}.

Lemma termT_msg1 E l kA kB (nA : term) :
  ↑cryptoN.@"nsl" ⊆ E →
  nsl_ctx -∗
  nsl_key Init kA -∗
  stermT l nA -∗
  termT Pub (TKey Enc kB) -∗
  guarded (l = Sec) (nsl_key Resp kB) ={E}=∗
  ▷ termT Pub (TEnc kB (Spec.tag "m1" (Spec.of_list [nA; TKey Enc kA]))).
Proof.
iIntros (?) "#ctx #HkA #HnA #HkB_lo #HkB_hi".
iMod (nsl_key_elim with "ctx HkA") as "# (?&?&?)" => //.
iMod (nsl_key_elimG with "ctx HkB_hi") as "# (?&?&?&?)" => //.
do 2![iModIntro].
iApply termT_tag_aenc_pub_secG; eauto.
  iApply termT_of_list => /=.
  iSplit; first by iApply stermT_termT.
  iSplit => //.
  by iApply (@sub_termT _ _ _ Pub) => //.
case: l => //=; iModIntro; by iExists _, _; eauto.
Qed.

Lemma termT_msg2 E l kA kB nA nB :
  ↑cryptoN.@"nsl" ⊆ E →
  nsl_ctx -∗
  ▷ termT Pub (TKey Enc kA) -∗
  guarded (l = Sec) (nsl_key Init kA) -∗
  nsl_key Resp kB -∗
  stermT l nA -∗
  stermT l nB -∗
  guarded (l = Sec) (session nsl_sess_name Resp kA kB nA nB) ={E}=∗
  ▷ termT Pub (TEnc kA (Spec.tag "m2" (Spec.of_list [nA; nB; TKey Enc kB]))).
Proof.
iIntros (?) "#ctx #HkA_enc #HkA #HkB #HnA #HnB #fragB".
iMod (nsl_key_elim  with "ctx HkB") as "# (?&?&?&?)" => //.
iMod (nsl_key_elimG with "ctx HkA") as "# (?&?&?)"   => //.
do !iModIntro.
iApply termT_tag_aenc_pub_secG; eauto.
  rewrite termT_of_list /=.
  iSplit; first by iApply stermT_termT.
  iSplit; first by iApply stermT_termT.
  by iSplit; first iApply sub_termT_pub.
by iIntros "!> -> /="; iExists _, _, _; do ![iSplit => //].
Qed.

Lemma msg1_pred_elimG E l (ts : list term) kA kB nA :
  ↑cryptoN.@"nsl" ⊆ E →
  ts !! 0 = Some nA →
  ts !! 1 = Some (TKey Enc kA) →
  nsl_ctx -∗
  termT l (Spec.of_list ts) -∗
  guarded (l = Sec) (msg1_pred kB (Spec.of_list ts)) ={E}=∗
  stermT l nA ∧
  ▷ termT Pub (TKey Enc kA) ∧
  guarded (l = Sec) (nsl_key Init kA).
Proof.
iIntros (? get_nA get_kA) "#ctx #term_ts mP".
rewrite termT_of_list.
iPoseProof (big_sepL_lookup with "term_ts") as "HnA"; first exact: get_nA.
iPoseProof (big_sepL_lookup with "term_ts") as "HkA"; first exact: get_kA.
case: l => /=; first by iModIntro; rewrite stermT_eq; eauto.
iDestruct "mP" as (nA' kA') "{HnA HkA} (%e & HnA & #HkA)".
move/Spec.of_list_inj: e get_nA get_kA => -> [] -> [] ->; eauto.
by iMod (nsl_key_elim with "ctx HkA") as "(?&?&?)" => //; eauto.
Qed.

Lemma msg2_pred_elimG `{Decision G} (ts : list term) kA kB nA nB :
  ts !! 0 = Some nA →
  ts !! 1 = Some nB →
  ts !! 2 = Some (TKey Enc kB) →
  guarded G (msg2_pred kA (Spec.of_list ts)) -∗
  guarded G (stermT Sec nA ∧ stermT Sec nB ∧
             session nsl_sess_name Resp kA kB nA nB).
Proof.
iIntros (get_nA get_nB get_kB) "mP".
rewrite /guarded; case: decide => //= _.
iDestruct "mP" as (nA' nB' kB') "(%e_m & nAP & nBP & frag)".
move/Spec.of_list_inj: e_m get_nA get_nB get_kB => -> /= [] -> [] -> [] ->.
by eauto.
Qed.

Lemma msg3_pred_elimG l kA kB nA nB :
  guarded (l = Sec) (msg3_pred kB nB) -∗
  guarded (l = Sec) (session nsl_sess_name Resp kA kB nA nB) -∗
  guarded (l = Sec) (session nsl_sess_name Init kA kB nA nB).
Proof.
iIntros "#HnB #sess -> /=".
by iApply "HnB"; iApply "sess".
Qed.

Lemma wp_initiator kA kB (nA : term) l E Ψ :
  ↑cryptoN.@"nsl" ⊆ E →
  nsl_ctx -∗
  stermT l nA -∗
  (∀ nB, guarded (l = Sec) (nsl_sess_inv Init kA kB nA nB)) -∗
  crypto_meta_token nA (↑cryptoN.@"nsl") -∗
  nsl_key Init kA -∗
  termT Pub (TKey Enc kB) -∗
  guarded (l = Sec) (nsl_key Resp kB) -∗
  (∀ onB : option term,
      (if onB is Some nB then
         stermT l nB ∗
         guarded (l = Sec) (nsl_sess_inv Resp kA kB nA nB)
       else True) -∗
      Ψ (repr onB)) -∗
  WP initiator (TKey Dec kA) (TKey Enc kA) (TKey Enc kB) nA #() @ E
     {{ Ψ }}.
Proof.
rewrite /initiator.
iIntros (?) "#ctx #HnA inv_nA unreg #HkA #HkB_lo #HkB_hi Hpost".
iMod (nsl_key_elim  with "ctx HkA") as "#HkA_inv" => //.
iMod (nsl_key_elimG with "ctx HkB_hi") as "#HkB_inv" => //.
wp_list (_ :: _ :: []).
wp_term_of_list.
wp_tenc => /=.
iMod (termT_msg1 with "ctx HkA HnA HkB_lo HkB_hi") as "#Hm1" => //.
wp_pures; wp_bind (send _); iApply wp_send; eauto.
iClear "Hm1"; wp_pures; wp_bind (recv _); iApply wp_recv.
iIntros (m2) "#Hm2"; wp_tdec m2; last protocol_failure.
wp_list_of_term m2; last protocol_failure.
wp_lookup nA' enA'; last protocol_failure.
wp_lookup nB  enB; last protocol_failure.
wp_lookup pkB' epkB'; last protocol_failure.
wp_eq_term e; last protocol_failure; subst nA'.
wp_eq_term e; last protocol_failure; subst pkB'.
wp_tenc.
iDestruct (termT_tag_adec_pub_sec with "Hm2 []")
    as (lm2) "{Hm2} [#Hm2 #sessB]".
  by iDestruct "HkA_inv" as "(?&?&?)".
wp_pures.
iPoseProof (msg2_pred_elimG with "sessB")
  as "{sessB} (HnA' & HnB & sessB)"; eauto.
rewrite termT_of_list.
iPoseProof (big_sepL_lookup with "Hm2") as "m2_nA"; first exact: enA'.
iPoseProof (big_sepL_lookup with "Hm2") as "m2_nB"; first exact: enB.
iPoseProof (big_sepL_lookup with "Hm2") as "m2_pkB"; first exact: epkB'.
iAssert (⌜lm2 = l⌝)%I as "->".
  case: l lm2 => [] [] //=.
    by iDestruct (stermT_agree with "HnA HnA'") as "%".
  rewrite stermT_eq; iDestruct "HnA" as "[_ #contra]".
  by iDestruct ("contra" with "m2_nA") as "[]".
iSpecialize ("inv_nA" $! nB).
iMod (session_beginG (l = Sec) with "[] inv_nA [unreg]")
    as "[#sessA close]" => //.
- by iDestruct "ctx" as "[??]".
- by iIntros "_".
iMod ("close" with "sessB") as "inv_resp" => //=.
wp_bind (send _); iApply wp_send.
  iModIntro.
  iDestruct "HkB_inv" as "(? & ? & ? & ?)".
  iApply (termT_tag_aenc_pub_secG _ l) => //; eauto.
  iIntros "!> -> !> %nA' %kA' #sessB'".
  iDestruct (session_agree with "sessB' sessB") as "/= %e" => //.
  by case: e => [] -> [] _ [] ->.
wp_pures; iApply ("Hpost" $! (Some nB)); iFrame.
by case: (l); rewrite // [stermT Pub nB]stermT_eq.
Qed.

Lemma wp_responder kB E Ψ :
  ↑cryptoN.@"nsl" ⊆ E →
  nsl_ctx -∗
  nsl_key Resp kB -∗
  (∀ ot : option (term * term * term),
      (if ot is Some (pkA, nA, nB) then
         ∃ l kA,
           ⌜pkA = TKey Enc kA⌝ ∗
           termT Pub pkA ∗
           stermT l nA ∗
           stermT l nB ∗
           guarded (l = Sec) (nsl_sess_inv Init kA kB nA nB)
       else True) -∗
       Ψ (repr ot)) -∗
  WP responder (TKey Dec kB) (TKey Enc kB) #() @ E {{ Ψ }}.
Proof.
iIntros (?) "#ctx #HkB Hpost".
rewrite /responder; wp_pures.
wp_bind (recv _); iApply wp_recv; iIntros (m1) "#Hm1".
wp_tdec m1; last protocol_failure.
wp_list_of_term m1; last protocol_failure.
wp_lookup nA enA; last protocol_failure.
wp_lookup pkA epkA; last protocol_failure.
wp_is_key_eq kt kA et; last protocol_failure; subst pkA.
wp_pures.
case: (bool_decide_reflect (_ = repr_key_type Enc)); last protocol_failure.
case: kt epkA=> // epkA _.
iMod (nsl_key_elim with "ctx HkB") as "#HkB_inv" => //.
iPoseProof "HkB_inv" as "(? & ? & HkB_m1 & HkB_m3)".
wp_pures.
iDestruct (termT_tag_adec_pub_sec with "Hm1 []")
  as (lm1) "{Hm1} [Hm1 #sessA]"; eauto.
wp_pures; wp_bind (gen _); iApply (wp_gen _ lm1 kA kB nA).
iIntros (nB) "unreg #HnB inv".
wp_pures.
wp_list (_ :: _ :: _ :: []); wp_term_of_list.
wp_tenc; wp_pures.
iMod (session_beginG with "[] inv [unreg]") as "[#sessB close]" => //.
- by iDestruct "ctx" as "[??]".
- by iIntros "_".
iMod (msg1_pred_elimG with "ctx Hm1 sessA") as "# (HnA & HkA_enc & HkA)" => //.
iMod (termT_msg2 with "ctx HkA_enc HkA HkB HnA HnB sessB") as "#Hm2" => //.
wp_bind (send _); iApply wp_send => //.
wp_pures; wp_bind (recv _); iApply wp_recv; iIntros (m3) "#Hm3".
wp_tdec m3; last protocol_failure.
iDestruct (termT_tag_adec_pub_sec with "Hm3 [//]")
  as (lm3) "{Hm3} [#Hm3 #Hprot3]".
wp_eq_term e; last protocol_failure; subst m3.
iAssert (⌜lm1 ⊑ lm3⌝)%I as "%lm1_lm3".
  by iDestruct "HnB" as "[_ #Hmin]"; iApply "Hmin".
iAssert (guarded (lm1 = Sec) (msg3_pred kB nB)) as "{Hprot3 Hm3} Hm3".
  iIntros "->"; by case: lm3 lm1_lm3.
clear lm1_lm3 lm3.
iPoseProof (msg3_pred_elimG with "Hm3 sessB") as "{sessA} sessA" => //=.
iMod ("close" with "sessA") as "inv".
wp_pures.
iApply ("Hpost" $! (Some (_, _, _))).
by iExists lm1, _; do 4![iSplit => //].
Qed.

End NSL.
