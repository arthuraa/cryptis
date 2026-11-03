From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import auth gset.
From iris.algebra.lib Require Import frac_auth.
From iris.heap_lang Require Import notation proofmode adequacy.
From iris.heap_lang.lib Require Import par assert.
From cryptis Require Import lib cryptis primitives tactics role adequacy.
From cryptis.examples Require Import hmqv.
From cryptis.lib Require Import hmqv.
From cryptis.primitives Require Import attacker.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * HMQV: injective agreement

    Alice, the initiator, and Bob, the responder, run sessions in parallel
    until the attacker tells each of them to stop.  Each talks to whatever peer
    the attacker picks -- Alice connects to the identity that the attacker
    names, Bob answers the identity that the first message claims -- and only
    keeps track of the sessions with the other: Alice records the key of each
    session with Bob, and Bob records the key of each session with Alice as
    soon as he has answered, noting whether Alice confirmed it.  Once all
    sessions are over, every key that Bob saw confirmed must be one of Alice's
    keys, each of Alice's keys must be one that Bob recorded, and no list may
    repeat a key.  So each session that Bob completes with Alice
    matches one of hers, no two of his match the same one, and the keys that
    Alice has but Bob did not see confirmed come from sessions that Bob did run
    with her, but whose last message never reached him.

*)

Class commitG Σ := CommitG {
  #[local] commitG_frac :: inG Σ (frac_authR (gsetR term));
  #[local] commitG_auth :: inG Σ (authR (gsetUR term));
}.

Definition commitΣ : gFunctors :=
  #[GFunctor (frac_authR (gsetR term)); GFunctor (authR (gsetUR term))].

#[global] Instance subG_commitG Σ : subG commitΣ Σ → commitG Σ.
Proof. solve_inG. Qed.

Section Game.

Context `{!cryptisGS Σ, !heapGS Σ, !spawnG Σ, !hmqvGS Σ, !commitG Σ}.
Abbreviation iProp := (iProp Σ).

Implicit Types (p_a p_b : nonce) (rl : role) (si : sess_info).
Implicit Types (k : term) (ks : list term) (rs : list (term * bool)) (q : Qp).

Definition gameN := nroot.@"game".

(** Each party commits to the keys of its sessions in a ledger.  The witnesses
    [committed γw k] are persistent, and the fragments [commits γ q X] are split
    among the party's sessions: once all of them are back, the committed keys
    are the keys of those sessions. *)
Definition committed γw k : iProp := own γw (◯ ({[k]} : gset term)).

Definition commits γ q (X : gset term) : iProp := own γ (◯F{q} X).

Definition ledger N γ γw : iProp :=
  inv N (∃ X : gset term, own γ (●F X) ∗ own γw (● X)).

(* What a party receives from its peer: the peer's commitment to the key.  Each
   party only commits in the sessions that it runs with the other. *)
Definition agree_pred γaw γbw p_a p_b p_a' p_b' si rl : iProp :=
  (if rl is Resp then ⌜p_b' = p_b⌝ → committed γaw (si_key si)
   else ⌜p_a' = p_a⌝ → committed γbw (si_key si))%I.

Lemma ledger_alloc N : ⊢ |={⊤}=> ∃ γ γw, ledger N γ γw ∗ commits γ 1 ∅.
Proof.
iMod (own_alloc (●F ∅ ⋅ ◯F ∅)) as (γ) "[auth frag]".
{ by apply: frac_auth_valid. }
iMod (own_alloc (● (∅ : gset term))) as (γw) "auth_w".
{ by apply auth_auth_valid. }
iMod (inv_alloc N _ (∃ X : gset term, own γ (●F X) ∗ own γw (● X))
        with "[auth auth_w]") as "#inv".
{ iNext. iExists ∅. iFrame. }
iModIntro. iExists γ, γw. by iFrame "inv frag".
Qed.

Lemma commit_update (X : gset term) k : (X, ∅) ~l~> ({[k]} ∪ X, {[k]}).
Proof.
rewrite -{2}(union_empty_r_L {[k]}) -!gset_op.
by apply: op_local_update_discrete.
Qed.

Lemma commits_split γ q :
  commits γ q ∅ -∗ commits γ (q / 2) ∅ ∗ commits γ (q / 2) ∅.
Proof.
rewrite /commits -own_op -frac_auth_frag_op Qp.div_2 gset_op union_empty_l_L.
by iIntros "$".
Qed.

Lemma commits_join γ q X1 X2 :
  commits γ (q / 2) X1 -∗ commits γ (q / 2) X2 -∗ commits γ q (X1 ∪ X2).
Proof.
rewrite /commits -gset_op -{3}(Qp.div_2 q) frac_auth_frag_op own_op.
by iIntros "$ $".
Qed.

Lemma commit N γ γw q k :
  ledger N γ γw -∗
  commits γ q ∅ ={⊤}=∗
  commits γ q {[k]} ∗ committed γw k.
Proof.
iIntros "#inv frag".
iInv N as (X) ">[auth auth_w]" "close".
iMod (own_update_2 with "auth frag") as "[auth frag]".
{ apply: frac_auth_update. exact: commit_update. }
iMod (own_update _ _ (● ({[k]} ∪ X) ⋅ ◯ {[k]}) with "auth_w")
  as "[auth_w w]".
{ apply: auth_update_alloc. exact: commit_update. }
iMod ("close" with "[auth auth_w]") as "_"; first by iExists _; iFrame.
by iFrame.
Qed.

Lemma commits_full N γ γw X ks :
  ledger N γ γw -∗
  commits γ 1 X -∗
  ([∗ list] k ∈ ks, committed γw k) ={⊤}=∗
  ⌜Forall (.∈ X) ks⌝.
Proof.
iIntros "#inv frag #ws".
iInv N as (X') ">[auth auth_w]" "close".
iDestruct (own_valid_2 with "auth frag") as %->%frac_auth_agree_L.
iAssert ⌜Forall (.∈ X) ks⌝%I as %sub.
{ rewrite Forall_forall. iIntros (k k_ks).
  iDestruct (big_sepL_elem_of with "ws") as "w"; first exact: k_ks.
  iDestruct (own_valid_2 with "auth_w w")
    as %[sub _]%auth_both_valid_discrete.
  iPureIntro. move: sub. rewrite gset_included. set_solver. }
iMod ("close" with "[auth auth_w]") as "_"; first by iExists _; iFrame.
by iModIntro.
Qed.

(* A key of a session of role [rl], owned through the session's share. *)
Definition owned rl k : iProp := ∃ si,
  ⌜k = si_key si⌝ ∗ ⌜session_of rl si⌝ ∗
  term_token (si_share_of rl si) (↑gameN).

Lemma owned_excl rl k : owned rl k -∗ owned rl k -∗ False.
Proof.
iIntros "(%si1 & -> & %s1 & tok1) (%si2 & %e & %s2 & tok2)".
move/term_of_senc_key_inj: e => e.
have ? := session_of_key_inj s1 s2 e; subst si2.
iDestruct (term_token_disj with "tok1 tok2") as %dis.
pose proof (nclose_non_empty gameN). set_solver.
Qed.

Lemma owned_NoDup rl ks : ([∗ list] k ∈ ks, owned rl k) -∗ ⌜NoDup ks⌝.
Proof.
elim: ks => [|k ks IH] /=; first by iIntros "_ !%"; constructor.
iIntros "[own owns]".
iAssert ⌜k ∉ ks⌝%I as %k_ks.
{ iIntros (k_ks).
  iDestruct (big_sepL_elem_of_acc with "owns") as "[own' _]"; first exact: k_ks.
  iApply (owned_excl with "own own'"). }
iDestruct (IH with "owns") as %?. iPureIntro. by constructor.
Qed.

Lemma honest_key_secrecy rl p_a p_b si :
  □ (public p_a ↔ ▷ False) -∗
  □ (public p_b ↔ ▷ False) -∗
  □ (¬ released_session si) -∗
  session rl p_a p_b si -∗
  public (si_key si) -∗
  ▷ False.
Proof.
iIntros "#s_pa #s_pb #un (-> & -> & _ & _ & [#comp|#s_k]) #p_k".
- iDestruct (compromised_static with "comp") as "[c|c]".
  + by iApply "s_pa".
  + by iApply "s_pb".
- iDestruct ("s_k" with "p_k") as "[#rel|[[#c _]|[#c _]]]".
  + iNext. by iApply "un".
  + by iApply "s_pa".
  + by iApply "s_pb".
Qed.

Definition session_res {A} `{!Repr A} (R : list A → iProp) (Q : A → iProp)
  (v : val) : iProp :=
  ∃ o : option A, ⌜v = repr o⌝ ∗
    (if o is Some x then R [x] ∗ Q x else R []).

(** Alice contacts whatever identity the attacker names, but only records the
    sessions with Bob. *)
Definition alice_session : val := λ: "c" "p_a" "P_a" "P_b",
  let: "P" := recv "c" in
  if: eq_term "P" "P_b" then
    bind: "r" := initiator "c" "p_a" "P_a" "P_b" (Tag gameN) in
    SOME (Fst "r")
  else
    initiator "c" "p_a" "P_a" "P" (Tag gameN);;
    NONE.

Lemma wp_alice_session c γa γaw γbw p_a p_b q :
  channel c -∗
  cryptis_ctx -∗
  hmqv_ctx -∗
  hmqv_pred gameN (agree_pred γaw γbw p_a p_b) -∗
  hmqv_key p_a -∗
  hmqv_key p_b -∗
  □ (public p_a ↔ ▷ False) -∗
  □ (public p_b ↔ ▷ False) -∗
  ledger (gameN.@"alice") γa γaw -∗
  commits γa q ∅ -∗
  WP alice_session c p_a (TExp g p_a) (TExp g p_b)
    {{ session_res (λ ks, commits γa q (list_to_set ks))
         (λ k, owned Init k ∗ committed γbw k) }}.
Proof.
iIntros "#? #? #? #? #? #? #s_pa #s_pb #led frag". wp_lam. wp_pures.
wp_apply wp_recv => //. iIntros "%P #p_P".
wp_eq_term e; last first.
{ wp_pures.
  wp_apply (wp_initiator_any _ _ _ _ _ (λ _ _, True)%I True%I with "[] []").
  - by iFrame "#".
  - iSplit => //. iIntros "%x_a %X_b _ _ !>". iSplit => //.
    iIntros "%p %eP". rewrite /agree_pred. iIntros "%ep". by subst.
  iIntros "%r _". wp_pures. iModIntro. iExists None. by iFrame. }
subst P. wp_pures.
wp_apply (wp_initiator _ _ _ _ _
            (λ x_a X_b,
               commits γa q {[si_key (init_si p_a x_a p_b X_b) : term]})
            (commits γa q ∅) with "[] [frag]")
  as "%r [[-> frag]|(%x_a & %X_b & -> & #sess & rel & tok & frag & gift)]".
- by iFrame "#".
- iSplit; first iExact "frag".
  iIntros "%x_a %X_b _ _".
  iMod (commit _ _ _ _ (si_key (init_si p_a x_a p_b X_b)) with "led frag")
    as "[frag #w]".
  iModIntro. iFrame "frag". by iIntros "_".
- wp_pures. iModIntro. iExists None. by iFrame.
- set si := init_si p_a x_a p_b X_b.
  iMod (unrelease Init with "rel") as "#un".
  iAssert (◇ committed γbw (si_key si))%I with "[gift]" as ">#w".
  { rewrite /agree_pred. iDestruct "gift" as "[#p_k|w]".
    - by iDestruct (honest_key_secrecy with "s_pa s_pb un sess p_k") as ">[]".
    - iModIntro. by iApply "w". }
  wp_pures. iModIntro.
  iExists (Some (si_key si : term)). iSplit => //=.
  rewrite union_empty_r_L. iFrame "frag w". iExists si. iSplit => //.
  iSplit; first by iPureIntro; exists p_a, x_a, p_b, X_b.
  iApply (term_token_drop with "tok"). solve_ndisj.
Qed.

(** Bob answers any identity, but only records the sessions with Alice, along
    with whether she confirmed them. *)
Definition bob_session : val := λ: "c" "p_b" "P_b" "P_a",
  let: "m1" := responder_listen "c" in
  let: "X" := Fst "m1" in
  let: "P" := Snd "m1" in
  if: eq_term "P" "P_a" then
    bind: "s" := responder_accept "c" "p_b" "P_b" "X" "P_a" (Tag gameN) in
    let: "k" := session_key (Fst "s") in
    let: "r" := responder_finish "c" (Fst "s") (Snd "s") (Tag gameN) in
    SOME ("k", match: "r" with NONE => #false | SOME <> => #true end)
  else
    responder_confirm "c" "p_b" "P_b" "X" "P" (Tag gameN);;
    NONE.

Lemma wp_bob_session c γb γaw γbw p_a p_b q :
  channel c -∗
  cryptis_ctx -∗
  hmqv_ctx -∗
  hmqv_pred gameN (agree_pred γaw γbw p_a p_b) -∗
  hmqv_key p_a -∗
  hmqv_key p_b -∗
  □ (public p_a ↔ ▷ False) -∗
  □ (public p_b ↔ ▷ False) -∗
  ledger (gameN.@"bob") γb γbw -∗
  commits γb q ∅ -∗
  WP bob_session c p_b (TExp g p_b) (TExp g p_a)
    {{ session_res (λ rs, commits γb q (list_to_set (map fst rs)))
         (λ r, owned Resp r.1 ∗ if r.2 then committed γaw r.1 else True) }}.
Proof.
iIntros "#? #? #? #? #? #? #s_pa #s_pb #led frag". wp_lam. wp_pures.
wp_apply wp_responder_listen; first by iSplit.
iIntros "%X %P [#p_X #p_P]". wp_pures.
wp_eq_term e; last first.
{ wp_pures.
  wp_apply (wp_responder_confirm_any _ _ _ _ _ _ (λ _, True)%I).
  { iFrame "#". iIntros "%x_b _ _ !>". iSplit => //.
    iIntros "%p %eP". rewrite /agree_pred. iIntros "%ep". by subst. }
  iIntros "%r _". wp_pures. iModIntro. iExists None. by iFrame. }
subst P. wp_pures.
wp_apply (wp_responder_accept _ (TExp g p_a) X p_b _ _
            (λ x_b, commits γb q {[si_key (resp_si p_a X p_b x_b) : term]})
            (commits γb q ∅) with "[frag]").
{ iFrame "#". iSplit; first iExact "frag". iIntros "%x_b _ _".
  iMod (commit _ _ _ _ (si_key (resp_si p_a X p_b x_b)) with "led frag")
    as "[frag #w]".
  iModIntro. iFrame "frag". iIntros "%p %e". rewrite /agree_pred.
  iIntros "%ep". subst p. iExact "w". }
iIntros "%r [[-> frag]|(%x_b & -> & state & rel & tok & frag)]".
{ wp_pures. iModIntro. iExists None. by iFrame. }
set si := resp_si p_a X p_b x_b.
iAssert (owned Resp (si_key si)) with "[tok]" as "own".
{ iExists si. iSplit => //.
  iSplit; first by iPureIntro; exists p_a, X, p_b, x_b.
  iApply (term_token_drop with "tok"). solve_ndisj. }
wp_pures. wp_apply wp_session_key. wp_pures.
wp_apply (wp_responder_finish with "[$state]"); first by iFrame "#".
iIntros "%r [->|(-> & #sess & gift)]".
- wp_pures. iModIntro. iExists (Some (si_key si : term, false)).
  iSplit => //=. rewrite union_empty_r_L. by iFrame.
- iMod (unrelease Resp si with "rel") as "#un".
  iAssert (◇ committed γaw (si_key si))%I with "[gift]" as ">#w".
  { rewrite /agree_pred /=.
    iDestruct "gift" as "[#p_k|w]"; last by (iModIntro; iApply "w").
    by iDestruct (honest_key_secrecy with "s_pa s_pb un sess p_k") as ">[]". }
  wp_pures. iModIntro. iExists (Some (si_key si : term, true)).
  iSplit => //=. rewrite union_empty_r_L. by iFrame.
Qed.

Definition sessions : val := rec: "loop" "c" "f" :=
  if: eq_term (recv "c") (TInt 0) then NONE
  else
    let: "r" := "f" #() ||| "loop" "c" "f" in
    match: Fst "r" with
      NONE => Snd "r"
    | SOME "k" => SOME ("k", Snd "r")
    end.

Lemma wp_sessions {A} `{!Repr A} c (f : val) (R : Qp → list A → iProp)
  (Q : A → iProp) q :
  channel c -∗
  □ (∀ q, R q [] -∗ R (q / 2)%Qp [] ∗ R (q / 2)%Qp []) -∗
  □ (∀ q xs1 xs2, R (q / 2)%Qp xs1 -∗ R (q / 2)%Qp xs2 -∗ R q (xs1 ++ xs2)) -∗
  □ (∀ q, R q [] -∗ WP f #() {{ session_res (R q) Q }}) -∗
  R q [] -∗
  WP sessions c f {{ v, ∃ xs, ⌜v = repr xs⌝ ∗ R q xs ∗
                            [∗ list] x ∈ xs, Q x }}.
Proof.
iIntros "#chan #split #join #f". iLöb as "IH" forall (q). iIntros "r".
wp_rec. wp_pures. wp_apply wp_recv => //. iIntros "%t _".
wp_eq_term e; wp_pures.
{ iModIntro. iExists []. rewrite repr_listE /=. by iFrame. }
iDestruct ("split" with "r") as "[r1 r2]".
wp_apply (wp_par (session_res (R (q / 2)%Qp) Q)
            (λ v, ∃ xs, ⌜v = repr xs⌝ ∗ R (q / 2)%Qp xs ∗
                        [∗ list] x ∈ xs, Q x)%I
            with "[r1] [r2]").
- by iApply "f".
- by iApply "IH".
- iIntros "%v1 %v2 [(%o & -> & r1) (%xs & -> & r2 & qs)] !>".
  case: o => [x|] /=; wp_pures; iModIntro.
  + iDestruct "r1" as "[r1 qx]". iExists (x :: xs).
    iSplit; first by rewrite [@repr_list]unlock. iFrame.
    by iApply ("join" with "r1 r2").
  + iExists xs. iSplit => //. iFrame.
    by iApply ("join" with "r1 r2").
Qed.

(* [wp_mem_list] wants a comparison that takes a step. *)
Definition teq : val := λ: "x" "y", eq_term "x" "y".

Lemma wp_teq (t1 t2 : term) :
  {{{ True }}} teq t1 t2 {{{ RET #(bool_decide (t1 = t2)); True }}}.
Proof.
iIntros "%Φ _ post". wp_lam. wp_pures. iApply wp_eq_term. by iApply "post".
Qed.

Definition all_in : val := rec: "loop" "xs" "ys" :=
  match: "xs" with
    NONE => #true
  | SOME "p" => mem_list teq (Fst "p") "ys" && "loop" (Snd "p") "ys"
  end.

Lemma wp_all_in ks1 ks2 :
  Forall (.∈ ks2) ks1 →
  {{{ True }}} all_in (repr ks1) (repr ks2) {{{ RET #true; True }}}.
Proof.
elim: ks1 => [|k ks1 IH] sub; iIntros "%Φ _ post".
- rewrite [repr (@nil term)]repr_listE. wp_rec. wp_pures. by iApply "post".
- rewrite [repr (k :: ks1)]repr_listE. wp_rec. wp_pures.
  move/Forall_cons: sub => [k_ks2 sub].
  wp_apply (wp_mem_list (A := term) teq k ks2); [exact: wp_teq|done|].
  iIntros "_". rewrite bool_decide_eq_true_2 //. wp_pures.
  by wp_apply IH.
Qed.

Definition no_dups : val := rec: "loop" "xs" :=
  match: "xs" with
    NONE => #true
  | SOME "p" => (~ mem_list teq (Fst "p") (Snd "p")) && "loop" (Snd "p")
  end.

Lemma wp_no_dups ks :
  NoDup ks →
  {{{ True }}} no_dups (repr ks) {{{ RET #true; True }}}.
Proof.
elim: ks => [|k ks IH] nd; iIntros "%Φ _ post".
- rewrite [repr (@nil term)]repr_listE. wp_rec. wp_pures. by iApply "post".
- rewrite [repr (k :: ks)]repr_listE. wp_rec. wp_pures.
  move/NoDup_cons: nd => [k_ks nd].
  wp_apply (wp_mem_list (A := term) teq k ks); [exact: wp_teq|done|].
  iIntros "_". rewrite bool_decide_eq_false_2 //. wp_pures.
  by wp_apply IH.
Qed.

(** Bob's records pair a key with whether Alice confirmed it. *)
Definition rec_key : val := λ: "r", Fst "r".
Definition rec_confirmed : val := λ: "r", Snd "r".

Definition answered : val := λ: "rs", map_list rec_key "rs".

Definition confirmed : val := λ: "rs",
  map_list rec_key (filter_list rec_confirmed "rs").

Lemma wp_answered rs :
  {{{ True }}} answered (repr rs) {{{ RET (repr (map fst rs)); True }}}.
Proof.
iIntros "%Φ _ post". wp_lam. iApply twp_wp.
iApply (twp_map_list fst with "[//]"); last by iIntros "_"; iApply "post".
apply/Forall_forall => - [k b] _. iIntros "%Ψ _ post". wp_lam. wp_pures.
by iApply "post".
Qed.

Lemma wp_confirmed rs :
  {{{ True }}}
    confirmed (repr rs)
  {{{ RET (repr (map fst (List.filter snd rs))); True }}}.
Proof.
iIntros "%Φ _ post". wp_lam.
wp_apply (wp_filter_list snd) => //.
{ move=> - [k b]. iIntros "%Ψ _ post". wp_lam. wp_pures. by iApply "post". }
iIntros "_". iApply twp_wp.
iApply (twp_map_list fst with "[//]"); last by iIntros "_"; iApply "post".
apply/Forall_forall => - [k b] _. iIntros "%Ψ _ post". wp_lam. wp_pures.
by iApply "post".
Qed.

Lemma NoDup_confirmed rs :
  NoDup (map fst rs) → NoDup (map fst (List.filter snd rs)).
Proof.
elim: rs => [|[k b] rs IH] //= /NoDup_cons [k_rs /IH nd].
case: b => //=. apply: NoDup_cons_2 => // k_conf. apply: k_rs.
move: k_conf; rewrite !list_elem_of_In !in_map_iff.
case=> - [k' b'] [/= <- /filter_In [in_rs _]]. by exists (k', b').
Qed.

Lemma owned_answered rs :
  ([∗ list] r ∈ rs, owned Resp r.1) -∗ [∗ list] k ∈ map fst rs, owned Resp k.
Proof.
elim: rs => [|r rs IH] /=; first by iIntros.
iIntros "[$ ?]". by iApply IH.
Qed.

Lemma committed_confirmed γw rs :
  ([∗ list] r ∈ rs, if (r : term * bool).2 then committed γw r.1 else True) -∗
  [∗ list] k ∈ map fst (List.filter snd rs), committed γw k.
Proof.
elim: rs => [|[k [] ] rs IH] /=; first by iIntros.
- iIntros "[$ ?]". by iApply IH.
- iIntros "[_ ?]". by iApply IH.
Qed.

Definition game : val := λ: "c",
  let: "k_a" := mk_lt_key #() in
  let: "k_b" := mk_lt_key #() in
  let: "p_a" := Fst "k_a" in
  let: "P_a" := Snd "k_a" in
  let: "p_b" := Fst "k_b" in
  let: "P_b" := Snd "k_b" in
  send "c" "P_a";;
  send "c" "P_b";;
  let: "res" :=
    sessions "c" (λ: <>, alice_session "c" "p_a" "P_a" "P_b") |||
    sessions "c" (λ: <>, bob_session "c" "p_b" "P_b" "P_a") in
  let: "ks_a" := Fst "res" in
  let: "ans_b" := answered (Snd "res") in
  let: "conf_b" := confirmed (Snd "res") in
  assert: (all_in "conf_b" "ks_a" && all_in "ks_a" "ans_b" &&
           no_dups "ks_a" && no_dups "ans_b" && no_dups "conf_b").

Lemma wp_game c :
  cryptis_ctx -∗
  channel c -∗
  hmqv_ctx -∗
  hmqv_token ⊤ -∗
  WP game c {{ _, True }}.
Proof.
iIntros "#ctx #chan #? tok"; rewrite /game; wp_pures.
wp_apply wp_mk_lt_key => //.
iIntros "%p_a (#key_a & s_pa & #p_Pa & _)". wp_pures.
wp_apply wp_mk_lt_key => //.
iIntros "%p_b (#key_b & s_pb & #p_Pb & _)". wp_pures.
iMod (freeze_secret with "s_pa") as "#s_pa".
iMod (freeze_secret with "s_pb") as "#s_pb".
iMod (ledger_alloc (gameN.@"alice")) as (γa γaw) "[#led_a frag_a]".
iMod (ledger_alloc (gameN.@"bob")) as (γb γbw) "[#led_b frag_b]".
iMod (hmqv_pred_set gameN (agree_pred γaw γbw p_a p_b) with "tok")
  as "[#? _]";
  first solve_ndisj.
wp_apply wp_send => //. wp_pures.
wp_apply wp_send => //. wp_pures.
wp_apply (wp_par
  (λ v, ∃ ks, ⌜v = repr ks⌝ ∗ commits γa 1 (list_to_set ks) ∗
              [∗ list] k ∈ ks, owned Init k ∗ committed γbw k)%I
  (λ v, ∃ rs, ⌜v = repr rs⌝ ∗ commits γb 1 (list_to_set (map fst rs)) ∗
              [∗ list] r ∈ rs, owned Resp r.1 ∗
                  if (r : term * bool).2 then committed γaw r.1 else True)%I
  with "[frag_a] [frag_b]").
- wp_pures.
  iApply (wp_sessions _ _ (λ q ks, commits γa q (list_to_set ks))
            with "chan [] [] [] frag_a").
  + iIntros "!> %q frag". by iApply commits_split.
  + iIntros "!> %q %ks1 %ks2 f1 f2". rewrite list_to_set_app_L.
    by iApply (commits_join with "f1 f2").
  + iIntros "!> %q frag". wp_pures. by iApply wp_alice_session.
- wp_pures.
  iApply (wp_sessions _ _ (λ q rs, commits γb q (list_to_set (map fst rs)))
            with "chan [] [] [] frag_b").
  + iIntros "!> %q frag". by iApply commits_split.
  + iIntros "!> %q %rs1 %rs2 f1 f2". rewrite map_app list_to_set_app_L.
    by iApply (commits_join with "f1 f2").
  + iIntros "!> %q frag". wp_pures. by iApply wp_bob_session.
- iIntros "%v1 %v2 [(%ks_a & -> & frag_a & owns_a) (%rs & -> & frag_b & owns_b)]
           !>".
  rewrite !big_sepL_sep.
  iDestruct "owns_a" as "[owns_a ws_a]". iDestruct "owns_b" as "[owns_b ws_b]".
  iDestruct (owned_NoDup with "owns_a") as %nd_a.
  iDestruct (owned_answered with "owns_b") as "owns_b".
  iDestruct (owned_NoDup with "owns_b") as %nd_b.
  iDestruct (committed_confirmed with "ws_b") as "ws_b".
  iMod (commits_full with "led_a frag_a ws_b") as %sub_a.
  iMod (commits_full with "led_b frag_b ws_a") as %sub_b.
  wp_pures. wp_apply wp_answered => //. iIntros "_".
  wp_pures. wp_apply wp_confirmed => //. iIntros "_".
  wp_pures. wp_apply wp_assert.
  wp_apply wp_all_in => //.
  { apply: (Forall_impl _ _ _ sub_a) => k. by rewrite elem_of_list_to_set. }
  iIntros "_". wp_pures.
  wp_apply wp_all_in => //.
  { apply: (Forall_impl _ _ _ sub_b) => k. by rewrite elem_of_list_to_set. }
  iIntros "_". wp_pures.
  wp_apply wp_no_dups => //. iIntros "_". wp_pures.
  wp_apply wp_no_dups => //. iIntros "_". wp_pures.
  by wp_apply wp_no_dups; first exact: NoDup_confirmed.
Qed.

End Game.

Definition F : gFunctors :=
  #[heapΣ; spawnΣ; cryptisΣ; hmqvΣ; commitΣ].

Lemma hmqv_agreement σ₁ σ₂ (v : val) t₂ e₂ :
  rtc erased_step ([run_network game], σ₁) (t₂, σ₂) →
  e₂ ∈ t₂ →
  not_stuck e₂ σ₂.
Proof.
have ? : heapGpreS F by apply _.
apply (adequate_not_stuck NotStuck _ _ (λ v _, True)) => //.
apply: cryptis_adequacy.
iIntros (? ? c) "#ctx #chan (_ & _ & _ & hash)".
iMod (hmqvGS_alloc with "hash") as (?) "(#? & tok & _)"; eauto.
by iApply (wp_game with "ctx chan [//] tok").
Qed.
