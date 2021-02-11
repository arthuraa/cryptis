From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl namespace_map frac.
From iris.base_logic.lib Require Import auth.
From iris.heap_lang Require Import notation proofmode.
From crypto Require Import lib guarded term crypto primitives tactics session.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*

A --> B: nA, vk(A)
B --> A: {nA, nB, vk(A)}_sk(B)
A --> B: {nA, nB, vk(B)}_sk(A)

*)


Section CR.

Context `{!cryptoG Σ, !heapG Σ}.
Notation iProp := (iProp Σ).

Implicit Types t : term.
Implicit Types s : session_view.
Implicit Types l : level.
Implicit Types rl : role.

Class crG := {
  in_cr_sessG :> sessionG Σ;
  in_cr_honestG :> inG Σ (authR (prodUR (gsetUR term) (gsetUR term)));
  cr_sess_name : gname;
  cr_honest_name : gname;
}.

Context `{!crG}.

Global Instance cr_honest_authG : authG Σ (prodUR (gsetUR term) (gsetUR term)).
Proof. constructor; apply _. Qed.

Definition cr_honest_proj rl : gset term * gset term → gset term :=
  if rl is Init then fst else snd.

Definition cr_res_of_key rl k : gset term * gset term :=
  if rl is Init then ({[k]}, ∅) else (∅, {[k]}).

Lemma cr_res_of_key_included rl k Ks :
  cr_res_of_key rl k ≼ Ks ↔
  k ∈ cr_honest_proj rl Ks.
Proof.
case: rl Ks=> [] [K1 K2] /=;
rewrite pair_included !gset_included;
split; intuition set_solver.
Qed.

Definition cr_key rl (k : term) : iProp :=
  auth_own cr_honest_name (cr_res_of_key rl k).

Global Instance cr_key_persistent rl k : Persistent (cr_key rl k).
Proof. case: rl; apply _. Qed.

Definition msg2_pred kB t : iProp :=
  ∃ nA nB kA,
    ⌜t = Spec.of_list [nA; nB; TKey Dec kA]⌝ ∧
    session cr_sess_name Resp kA kB nA nB.

Global Instance msg2_pred_persistent kB t :
  Persistent (msg2_pred kB t).
Proof. by apply _. Qed.

Lemma msg2_pred_elimG `{Decision G} (ts : list term) kA kB nA nB :
  ts !! 0 = Some nA →
  ts !! 1 = Some nB →
  ts !! 2 = Some (TKey Dec kA) →
  guarded G (msg2_pred kB (Spec.of_list ts)) -∗
  guarded G (session cr_sess_name Resp kA kB nA nB).
Proof.
iIntros (ts_0 ts_1 ts_2) "tsP".
rewrite /guarded; case: decide => //= _.
iDestruct "tsP" as (nA' nB' kA') "[%e #sess]".
by move/Spec.of_list_inj: e ts_0 ts_1 ts_2 => -> [] -> [] -> [] ->.
Qed.

(* FIXME: the □ should not be needed, but removing it causes TC resolution to
diverge. *)
Definition msg3_pred kA m3 : iProp :=
  □ ∃ nA nB kB,
    ⌜m3 = Spec.of_list [nA; nB; TKey Dec kB]⌝ ∧
    session cr_sess_name Init kA kB nA nB.

Global Instance msg3_pred_persistent kA m3 :
  Persistent (msg3_pred kA m3).
Proof. by apply _. Qed.

Lemma msg3_pred_elimG `{Decision G} (ts : list term) kA kB nA nB :
  ts !! 0 = Some nA →
  ts !! 1 = Some nB →
  ts !! 2 = Some (TKey Dec kB) →
  guarded G (msg3_pred kA (Spec.of_list ts)) -∗
  guarded G (session cr_sess_name Init kA kB nA nB).
Proof.
iIntros (ts_0 ts_1 ts_2) "tsP".
rewrite /guarded; case: decide => //= _.
iDestruct "tsP" as (nA' nB' kA') "[%e #sess]".
by move/Spec.of_list_inj: e ts_0 ts_1 ts_2 => -> [] -> [] -> [] ->.
Qed.

Definition cr_key_inv rl k : iProp :=
  termT Pub (TKey Dec k) ∗
  stermT Sec (TKey Enc k) ∗
  match rl with
  | Resp => tkey_predT (nroot.@"m2") (msg2_pred k) k
  | Init => tkey_predT (nroot.@"m3") (msg3_pred k) k
  end.
Arguments cr_key_inv : simpl never.

Global Instance cr_key_inv_persistent rl k :
  Persistent (cr_key_inv rl k).
Proof. rewrite /cr_key_inv; case: rl; apply _. Qed.

Lemma cr_key_inv_pub rl k : cr_key_inv rl k -∗ termT Pub (TKey Dec k).
Proof. by iDestruct 1 as "[??]". Qed.

Definition cr_keys_inv Ks : iProp := (
  [∗ list] rl ∈ [Init; Resp],
  [∗ set]  k  ∈ cr_honest_proj rl Ks,
    cr_key_inv rl k
)%I.

Lemma cr_keys_inv_elim rl k Ks :
  k ∈ cr_honest_proj rl Ks →
  cr_keys_inv Ks -∗
  cr_key_inv rl k.
Proof.
case: rl => [] /= k_Ks; iIntros "inv"; rewrite /cr_keys_inv /=.
- iDestruct "inv" as "[inv _]".
  by rewrite big_sepS_forall; iApply "inv".
- iDestruct "inv" as "(_ & inv & _)".
  by rewrite big_sepS_forall; iApply "inv".
Qed.

Variable cr_sess_inv : role → term → term → term → term → iProp.

Definition cr_inv : iProp :=
  session_inv cr_sess_name (cryptoN.@"cr") cr_sess_inv.

Definition cr_ctx : iProp :=
  session_ctx cr_sess_name (cryptoN.@"cr") cr_sess_inv ∧
  auth_ctx cr_honest_name (cryptoN.@"cr") id cr_keys_inv.

Lemma cr_key_elim E rl k :
  ↑cryptoN.@"cr" ⊆ E →
  cr_ctx -∗
  cr_key rl k ={E}=∗
  ▷ cr_key_inv rl k.
Proof.
iIntros (?) "[_ #ctx] #key".
iMod (auth_acc id cr_keys_inv with "[ctx key]") as "inv"; eauto.
iDestruct "inv" as (Ks) "(%k_K & #inv & close)".
iMod ("close" $! Ks with "[]") as "_"; first by iSplit; eauto.
move: k_K; rewrite cr_res_of_key_included /= => k_K.
by iIntros "!> !>"; iApply cr_keys_inv_elim; eauto.
Qed.

Lemma cr_key_elimG `{Decision G} E rl k :
  ↑cryptoN.@"cr" ⊆ E →
  cr_ctx -∗
  guarded G (cr_key rl k) ={E}=∗
  ▷ guarded G (cr_key_inv rl k).
Proof.
iIntros (?) "ctx key_k"; rewrite /guarded; case: decide => //= _.
by iApply (cr_key_elim with "ctx key_k").
Qed.

Variable send recv gen : val.

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None).

Definition initiator (skA pkA pkB nA : val) : val := λ: <>,
  let:  "m1"   := term_of_list [nA; pkA] in
  send  "m1";;
  bind: "m2"   := tdec (nroot.@"m2") pkB (recv #()) in
  bind: "m2"   := list_of_term "m2" in
  bind: "nA'"  := "m2" !! #0 in
  bind: "nB"   := "m2" !! #1 in
  bind: "pkA'" := "m2" !! #2 in
  if: eq_term "nA'" nA && eq_term "pkA'" pkA then
    let:  "m3" := term_of_list [nA; "nB"; pkB] in
    bind: "m3" := tenc (nroot.@"m3") skA "m3" in
    send "m3";;
    SOME "nB"
  else NONE.

Definition responder (skB pkB : val) : val := λ: <>,
  bind: "m1"   := list_of_term (recv #()) in
  bind: "nA"   := "m1" !! #0 in
  bind: "pkA"  := "m1" !! #1 in
  bind: "kt"   := is_key "pkA" in
  if: "kt" = repr Dec then
    let:  "nB"   := gen #() in
    bind: "m2"   := tenc (nroot.@"m2") skB (term_of_list ["nA"; "nB"; "pkA"]) in
    send  "m2";;
    bind: "m3"   := tdec (nroot.@"m3") "pkA" (recv #()) in
    bind: "m3"   := list_of_term "m3" in
    bind: "nA'"  := "m3" !! #0 in
    bind: "nB'"  := "m3" !! #1 in
    bind: "pkB'" := "m3" !! #2 in
    if: eq_term "nA'" "nA" && eq_term "nB'" "nB" && eq_term "pkB'" pkB then
      SOME ("pkA", "nA", "nB")
    else NONE
  else NONE.
Implicit Types Ψ : val → iProp.

Hypothesis wp_send : forall E t Ψ,
  ▷ termT Pub t -∗
  Ψ #() -∗
  WP send t @ E {{ Ψ }}.

Hypothesis wp_recv : forall E Ψ,
  (∀ t, termT Pub t -∗ Ψ t) -∗
  WP recv #() @ E {{ Ψ }}.

Hypothesis wp_gen : forall E kA kB nA Ψ,
  (∀ nB, cr_sess_inv Resp kA kB nA nB -∗
         crypto_meta_token nB (↑cryptoN.@"cr") -∗
         termT Pub nB -∗
         Ψ nB) -∗
  WP gen #() @ E {{ Ψ }}.

Lemma wp_initiator `{Decision G} kA kB nA E Ψ :
  ↑cryptoN.@"cr" ⊆ E →
  cr_ctx -∗
  termT Pub nA -∗
  (∀ nB, cr_sess_inv Init kA kB nA nB) -∗
  crypto_meta_token nA (↑cryptoN.@"cr") -∗
  cr_key Init kA -∗
  termT Pub (TKey Dec kB) -∗
  guarded G (cr_key Resp kB) -∗
  (∀ onB : option term,
      (if onB is Some nB then
         termT Pub nB ∗
         guarded G (cr_sess_inv Resp kA kB nA nB)
       else True) -∗
      Ψ (repr onB)) -∗
  WP initiator (TKey Enc kA) (TKey Dec kA) (TKey Dec kB) nA #() @ E
     {{ Ψ }}.
Proof.
rewrite /initiator.
iIntros (?) "#ctx #HnA inv_nA unreg #HkA #HkB_lo #HkB_hi Hpost".
iMod (cr_key_elim with "ctx HkA") as "#HkA_inv" => //.
iMod (cr_key_elimG with "ctx HkB_hi") as "#HkB_inv" => //.
wp_list (_ :: _ :: []).
wp_term_of_list.
wp_pures; wp_bind (send _); iApply wp_send.
  iModIntro.
  iApply termT_of_list => /=.
  iDestruct "HkA_inv" as "(?&?&?)".
  by do !iSplit.
wp_pures; wp_bind (recv _); iApply wp_recv.
iIntros (m2) "#Hm2"; wp_tdec m2; last protocol_failure.
wp_list_of_term m2; last protocol_failure.
wp_lookup nA' enA'; last protocol_failure.
wp_lookup nB  enB; last protocol_failure.
wp_lookup pkB' epkB'; last protocol_failure.
wp_eq_term e; last protocol_failure; subst nA'.
wp_eq_term e; last protocol_failure; subst pkB'.
iDestruct "HkB_inv" as "(_ & HkB_enc & Htag_m2)".
iPoseProof (termT_tag_adec_sec_pubG
              with "HkB_enc Htag_m2 HkB_lo Hm2") as "{Hm2} [Hm2 #fragB]".
rewrite termT_of_list.
iPoseProof (big_sepL_lookup with "Hm2") as "m2_nB"; first exact: enB.
wp_list (_ :: _ :: _ :: []); wp_term_of_list.
wp_tenc; wp_pures.
iPoseProof (msg2_pred_elimG with "fragB") as "{fragB} fragB"; eauto.
iMod (session_begin with "[] [inv_nA] [unreg]") as "[#sessA close]".
- by eauto.
- by iDestruct "ctx" as "[??]".
- by iApply "inv_nA".
- by eauto.
iAssert (|={E}=> ▷ guarded G (cr_sess_inv Resp kA kB nA nB))%I
    with "[close]" as ">inv".
  rewrite /guarded; case: decide => [_|//].
  by iApply "close".
wp_bind (send _); iApply wp_send.
  iModIntro.
  iDestruct "HkA_inv" as "(?&?&?)".
  iApply termT_tag_aenc_sec_pub => //.
  - by iApply stermT_termT.
  - by rewrite termT_of_list /=; do !iSplit.
  - iIntros "!> !>"; by iExists _, _, _; iSplit.
wp_pures; iApply ("Hpost" $! (Some nB)).
by iFrame.
Qed.

Lemma wp_responder kA kB E Ψ :
  ↑cryptoN.@"cr" ⊆ E →
  cr_ctx -∗
  cr_key Init kA -∗
  cr_key Resp kB -∗
  (∀ ot : option (term * term * term),
      (if ot is Some (pkA, nA, nB) then
         ∃ kA',
           ⌜pkA = TKey Dec kA'⌝ ∗
           termT Pub nA ∗
           termT Pub nB ∗
           termT Pub (TKey Dec kA') ∗
           guarded (kA' = kA) (cr_sess_inv Init kA kB nA nB)
       else True) -∗
       Ψ (repr ot)) -∗
  WP responder (TKey Enc kB) (TKey Dec kB) #() @ E {{ Ψ }}.
Proof.
iIntros (?) "#ctx #HkA #HkB Hpost".
iMod (cr_key_elim with "ctx HkA") as "# (?&?&?)" => //.
iMod (cr_key_elim with "ctx HkB") as "# (?&?&?)" => //.
rewrite /responder; wp_pures.
wp_bind (recv _); iApply wp_recv; iIntros (m1) "#Hm1".
wp_list_of_term m1; last protocol_failure.
wp_lookup nA enA; last protocol_failure.
wp_lookup pkA epkA; last protocol_failure.
rewrite termT_of_list.
iPoseProof (big_sepL_lookup with "Hm1") as "HnA"; first exact: enA.
iPoseProof (big_sepL_lookup with "Hm1") as "HpkA"; first exact: epkA.
iClear "Hm1".
wp_is_key_eq kt kA' et; last protocol_failure; subst pkA.
wp_pures.
case: (bool_decide_reflect (_ = repr_key_type Dec)); last protocol_failure.
case: kt epkA=> // epkA _.
wp_pures; wp_bind (gen _); iApply wp_gen; iIntros (nB) "inv token #HnB".
iMod (session_begin with "[] inv [token]") as "[#sessB close]".
- by eauto.
- by iDestruct "ctx" as "[??]".
- by eauto.
wp_list (_ :: _ :: _ :: []); wp_term_of_list.
wp_tenc; wp_pures; wp_bind (send _); iApply wp_send.
  iModIntro.
  iApply termT_tag_aenc_sec_pub.
  - by iApply stermT_termT.
  - by eauto.
  - by rewrite termT_of_list /=; do !iSplit.
  - iModIntro; iExists _, _, _; eauto.
wp_pures; wp_bind (recv _); iApply wp_recv; iIntros (m3) "#Hm3".
wp_tdec m3; last protocol_failure.
wp_list_of_term m3; last protocol_failure.
iAssert (▷^2 guarded (kA' = kA) (msg3_pred kA (Spec.of_list m3)))%I
    as "{Hm3} Hm3".
  rewrite /guarded; case: decide => [e|//]; subst kA'.
  by iPoseProof (termT_tag_adec_sec_pub kA (nroot.@"m3") with "[//] [//] [//] Hm3")
    as "[_ #sessA]".
wp_lookup nA' enA'; last protocol_failure.
wp_lookup nB' enB'; last protocol_failure.
wp_lookup pkB' epkB'; last protocol_failure.
wp_eq_term e; last protocol_failure; subst nA'.
wp_eq_term e; last protocol_failure; subst nB'.
wp_eq_term e; last protocol_failure; subst pkB'.
iPoseProof (msg3_pred_elimG with "Hm3") as "sessA" => //.
iAssert (|={E}=> ▷ (guarded (kA' = kA) (cr_sess_inv Init kA kB nA nB)))%I
    with "[close]" as ">inv".
  rewrite /guarded; case: decide => [->|//]; by iApply "close".
wp_pures; iApply ("Hpost" $! (Some (_, _, _))).
by iExists _; do ![iSplit=> //].
Qed.

End CR.
