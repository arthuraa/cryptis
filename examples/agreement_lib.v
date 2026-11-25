From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import auth gset.
From iris.algebra.lib Require Import frac_auth.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import par.
From cryptis Require Import lib cryptis primitives tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Agreement games: shared machinery

    Protocol-independent pieces of the injective-agreement games of
    [examples/hmqv/games] and [examples/opaque/games]:

    - a ledger in which a party commits to the keys of its sessions, which
      lets the game prove, once all of the party's sessions are back, that any
      key its peer was promised is one of them;

    - [sessions c f], which runs [f] in parallel as many times as the attacker
      wants and collects the results; and

    - list checks on terms ([all_in], [no_dups]), the projections of a
      responder's records of which sessions were confirmed ([answered],
      [confirmed]), and [excl_NoDup], which
      discharges [no_dups] for keys owned through exclusive tokens.

*)

Class commitG Σ := CommitG {
  #[local] commitG_frac :: inG Σ (frac_authR (gsetR term));
  #[local] commitG_auth :: inG Σ (authR (gsetUR term));
}.

Definition commitΣ : gFunctors :=
  #[GFunctor (frac_authR (gsetR term)); GFunctor (authR (gsetUR term))].

#[global] Instance subG_commitG Σ : subG commitΣ Σ → commitG Σ.
Proof. solve_inG. Qed.

Section AgreementLib.

Context `{!cryptisGS Σ, !heapGS Σ, !spawnG Σ, !commitG Σ}.
Abbreviation iProp := (iProp Σ).

Implicit Types (k : term) (ks : list term) (rs : list (term * bool)) (q : Qp).

(** Each party commits to the keys of its sessions in a ledger.  The witnesses
    [committed γw k] are persistent, and the fragments [commits γ q X] are split
    among the party's sessions: once all of them are back, the committed keys
    are the keys of those sessions. *)
Definition committed γw k : iProp := own γw (◯ ({[k]} : gset term)).

Definition commits γ q (X : gset term) : iProp := own γ (◯F{q} X).

Definition ledger N γ γw : iProp :=
  inv N (∃ X : gset term, own γ (●F X) ∗ own γw (● X)).

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

(** A list of exclusive resources on terms cannot repeat a term. *)
Lemma excl_NoDup (P : term → iProp) ks :
  □ (∀ k, P k -∗ P k -∗ False) -∗
  ([∗ list] k ∈ ks, P k) -∗ ⌜NoDup ks⌝.
Proof.
iIntros "#excl".
iInduction ks as [|k ks] "IH"; first by iIntros "_ !%"; constructor.
iIntros "/= [own owns]".
iAssert ⌜k ∉ ks⌝%I as %k_ks.
{ iIntros (k_ks).
  iDestruct (big_sepL_elem_of_acc with "owns") as "[own' _]"; first exact: k_ks.
  iApply ("excl" with "own own'"). }
iDestruct ("IH" with "owns") as %?. iPureIntro. by constructor.
Qed.

(** What one session hands back: [R] tracks the session's share of the party's
    ghost state, and [Q] what the game learns of its result, if any. *)
Definition session_res {A} `{!Repr A} (R : list A → iProp) (Q : A → iProp)
  (v : val) : iProp :=
  ∃ o : option A, ⌜v = repr o⌝ ∗
    (if o is Some x then R [x] ∗ Q x else R []).

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

(** A responder's records pair a key with whether the initiator confirmed
    it. *)
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

Lemma big_sepL_answered (P : term → iProp) (rs : list (term * bool)) :
  ([∗ list] r ∈ rs, P r.1) -∗ [∗ list] k ∈ map fst rs, P k.
Proof.
elim: rs => [|r rs IH] /=; first by iIntros.
iIntros "[$ ?]". by iApply IH.
Qed.

Lemma big_sepL_confirmed (P : term → iProp) (rs : list (term * bool)) :
  ([∗ list] r ∈ rs, if (r : term * bool).2 then P r.1 else True) -∗
  [∗ list] k ∈ map fst (List.filter snd rs), P k.
Proof.
elim: rs => [|[k [] ] rs IH] /=; first by iIntros.
- iIntros "[$ ?]". by iApply IH.
- iIntros "[_ ?]". by iApply IH.
Qed.

End AgreementLib.
