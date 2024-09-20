From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics role.
From cryptis Require Import session dh.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section RelChannel.

Notation rel_channelG Σ := (inG Σ (authR (max_prefix_listUR termO))).

Context `{!cryptisGS Σ, !heapGS Σ, !sessionGS Σ, !rel_channelG Σ}.
Notation iProp := (iProp Σ).

Implicit Types t : term.
Implicit Types rl : role.

Variable N : namespace.

Implicit Types Ψ : val → iProp.
Implicit Types γ : gname.
Implicit Types kA kB : term.
Implicit Types ts : list term.

Definition channel_state_auth k ts : iProp :=
  ∃ γ, term_meta k (N.@"channel") γ ∗
  own γ (● to_max_prefix_list ts ⋅ ◯ to_max_prefix_list ts).

Definition channel_state_frag k ts : iProp :=
  ∃ γ, term_meta k (N.@"channel") γ ∗ own γ (◯ to_max_prefix_list ts).

Definition rel_channel_send k l ts : iProp :=
  l ↦ #(length ts) ∗ minted (TKey Enc k) ∗ channel_state_auth k ts.

Definition rel_channel_recv k l ts : iProp :=
  l ↦ #(length ts) ∗ minted (TKey Dec k) ∗ channel_state_frag k ts.

Definition rel_channel_pred k t : iProp :=
  ∃ ts m γ, ⌜t = Spec.of_list [TInt (length ts); m]⌝ ∧
  term_meta k (N.@"channel") γ ∧
  own γ (◯ to_max_prefix_list (ts ++ [m])).

Definition rel_send : val := λ: "c" "k" "l" "m",
  let: "n" := !"l" in
  "l" <- "n" + #1;;
  send "c" (tenc N "k" (term_of_list [tint "n"; "m"])).

Definition rel_recv : val := rec: "loop" "c" "k" "l" :=
  let: "m" :=
    let: "m" := recv "c" in
    bind: "m" := tdec N "k" "m" in
    bind: "m" := list_of_term "m" in
    list_match: ["n"; "m"] := "m" in
    bind: "n" := to_int "n" in
    SOME ("n", "m") in
  match: "m" with
    NONE => "loop" "c" "k" "l"
  | SOME "m" => if: !"l" = Fst "m" then "l" <- !"l" + #1;; Snd "m"
                else "loop" "c" "k" "l"
  end.

Lemma wp_rel_send c k l m ts Ψ :
  channel c -∗
  enc_pred N rel_channel_pred -∗
  rel_channel_send k l ts -∗
  minted m -∗
  □ (public (TKey Dec k) → public m) -∗
  (rel_channel_send k l (ts ++ [m]) -∗ Ψ #()) -∗
  WP rel_send c (TKey Enc k) #l m {{ Ψ }}.
Proof.
iIntros "#chan_c #enc (Hl & #s_k & %γ & #k_γ & auth) #s_m #p_m post".
iMod (own_update with "auth") as "auth".
{ apply auth_update.
  apply (max_prefix_list_local_update _ (ts ++ [m])).
  by exists [m]. }
iAssert (own γ (◯ to_max_prefix_list (ts ++ [m]))) with "[auth]" as "#frag".
{ by iDestruct "auth" as "[??]". }
rewrite /rel_send. wp_pures; wp_load; wp_pures; wp_store.
wp_list. wp_bind (tint _). iApply wp_tint. wp_list.
wp_term_of_list. wp_tenc. iApply wp_send => //.
  iModIntro => /=.
  iApply public_TEncIS => //.
  - iModIntro. iExists ts, m, γ. do 2!iSplit => //.
    by rewrite minted_of_list /= minted_TInt; eauto.
  - iIntros "!> #p_k".
    rewrite public_of_list /= public_TInt; do 2!iSplit => //.
    by iApply "p_m".
iApply "post". rewrite /rel_channel_send app_length /= Nat2Z.inj_add /=. iFrame.
iSplit => //. by iExists γ; eauto.
Qed.

Tactic Notation "retry" constr(IH) constr(Hl) :=
  wp_pures; iApply (IH with Hl).

Lemma wp_rel_recv c k l ts Ψ :
  channel c -∗
  enc_pred N rel_channel_pred -∗
  rel_channel_recv k l ts -∗
  (∀ m, public m ∧ public (TKey Enc k) ∨
        minted m ∧
        □ (public (TKey Dec k) -∗ public m) ∧
        rel_channel_recv k l (ts ++ [m]) -∗ Ψ m) -∗
  WP rel_recv c (TKey Dec k) #l {{ Ψ }}.
Proof.
iIntros "#chan_c #enc (Hl & #s_k & %γ & #k_γ & #frag) post".
iLöb as "IH". wp_rec. wp_pures.
wp_bind (recv _). iApply wp_recv => //. iIntros "%m #p_m".
wp_pures. wp_tdec m; last by retry "IH" "Hl".
wp_pures. wp_list_of_term m; last by retry "IH" "Hl".
wp_pures. rewrite !subst_list_match /=.
wp_list_match => [ n {}m ->|_]; last by retry "IH" "Hl".
wp_bind (to_int _). iApply wp_to_int.
case: Spec.to_intP => [ {}n ->|_]; last by retry "IH" "Hl".
wp_pures. wp_load. wp_pures.
case: bool_decide_reflect => [[<- {n}]|_]; last by retry "IH" "Hl".
iDestruct (public_TEncE with "p_m [//]") as "{p_m IH} [[p_k p_m] |H]".
  rewrite public_of_list /=.
  iDestruct "p_m" as "(_ & p_m & _)".
  wp_pures. wp_load. wp_pures. wp_store. wp_pures. iModIntro.
  by iApply "post"; eauto.
iDestruct "H" as "(#mP & s_m & #p_m)".
wp_pures.
iDestruct "mP" as "(%ts' & %m' & %γ' & %e & k_γ' & frag')".
iPoseProof (term_meta_agree with "k_γ k_γ'") as "{k_γ'} <-".
case/Spec.of_list_inj: e => {m'} /Nat2Z.inj e <-.
iPoseProof (own_valid_2 with "frag frag'") as "%valid"; move: valid.
rewrite -auth_frag_op auth_frag_valid to_max_prefix_list_op_valid_L.
case => prefix; last first.
  case: prefix e => ? ->; rewrite !app_length /=; lia.
case: prefix => m' e_ts.
have ? : ts' = ts; last subst ts'.
  move: (f_equal (take (length ts)) e_ts).
  by rewrite take_app e take_app.
have ? : [m] = m'; last subst m'.
  move: (f_equal (drop (length ts)) e_ts).
  by rewrite !drop_app.
rewrite minted_of_list /=. iDestruct "s_m" as "(_ & s_m & _)".
wp_load. wp_pures. wp_store. wp_pures. iModIntro. iApply "post".
iRight. iSplit => //. iSplit.
  iIntros "!> #p_k". iSpecialize ("p_m" with "p_k").
  rewrite public_of_list /=. by iDestruct "p_m" as "(_ & ? & _)".
rewrite /rel_channel_recv app_length /= Nat2Z.inj_add. iFrame.
rewrite !minted_TKey; iSplit => //.
by iExists γ; eauto.
Qed.

End RelChannel.
