From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl namespace_map frac.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis Require Import session nsl dh.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section NSLDH.

Context `{!cryptisG Σ, !heapG Σ, !sessionG Σ}.
Notation iProp := (iProp Σ).

Implicit Types t : term.
Implicit Types rl : role.

Variable N : namespace.
Variable P : role → term → term → term → term → iProp.

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None).

Definition nsl_dh_init : val := λ: "c" "g" "skA" "pkA" "pkB",
  let: "a" := mkdh #() in
  let: "ga" := texp (tgroup "g") "a" in
  bind: "gb" := nsl_init (N.@"nsl") "c" "skA" "pkA" "pkB" "ga" in
  SOME (texp "gb" "a").

Definition nsl_dh_resp : val := λ: "c" "g" "skB" "pkB",
  let: "b" := mkdh #() in
  let: "gb" := texp (tgroup "g") "b" in
  bind: "res" := nsl_resp (N.@"nsl") "c" "skB" "pkB" "gb" in
  let: "pkA" := Fst "res" in
  let: "ga" := Snd "res" in
  SOME ("pkA", texp "ga" "b").

Implicit Types Ψ : val → iProp.
Implicit Types kA kB : term.

Definition nsl_dh_inv g rl ga gb kA kB : iProp :=
  P rl ga gb kA kB ∗
  match rl with
  | Init =>
    ∃ a, ⌜ga = TExp g [a]⌝ ∧
    □ ∀ b, (pterm (TExp g [a; b]) → ◇ pterm b)
  | Resp =>
    ∃ b, ⌜gb = TExp g [b]⌝ ∧
    □ ∀ a, (pterm (TExp g [a; b]) → ◇ pterm a)
  end%I.

Definition nsl_dh_ctx g γ :=
  nsl_ctx (@dh_meta _ _) (N.@"nsl") (nsl_dh_inv g) γ.

Lemma nsl_dh_alloc g E E' :
  ↑N ⊆ E →
  enc_pred_token E ={E'}=∗ ∃ γ, nsl_dh_ctx g γ.
Proof.
move=> sub; apply: nsl_alloc; solve_ndisj.
Qed.

Definition nsl_dh_fail (k : term) a : iProp :=
  ∃ k', dh_meta a (N.@"peer") k' ∧ corruption k k'.

Lemma pterm_nsl_dh1 g a k k' :
  sterm g -∗
  dh_seed (nsl_dh_fail k) a -∗
  dh_meta (TExp g [a]) (N.@"peer") k' -∗
  pterm (TExp g [a]) ↔ ▷ corruption k k'.
Proof.
iIntros "#gP #a_pred #meta"; iSplit.
- iIntros "#p_e".
  iDestruct (dh_seed_elim1 with "a_pred p_e") as (k'') "[meta' corr]".
  iModIntro.
  by iPoseProof (term_meta_agree with "meta meta'") as "<-".
- iIntros "#corr".
  iApply dh_pterm_TExp; eauto.
  by iExists k'; iModIntro; iModIntro; iSplit; eauto.
Qed.

Lemma pterm_nsl_dh2 g a k t :
  dh_seed (nsl_dh_fail k) a -∗
  pterm (TExp g [a; t]) -∗ ◇ pterm t.
Proof.
iIntros "#a_pred #p_e".
by iPoseProof (dh_seed_elim2 with "a_pred p_e") as ">[??]".
Qed.

Lemma wp_nsl_dh_init Q c γ g kA kB E Ψ :
  ↑cryptisN ⊆ E →
  ↑N ⊆ E →
  channel c -∗
  nsl_dh_ctx g γ -∗
  sterm g -∗
  pterm (TKey Enc kA) -∗
  pterm (TKey Enc kB) -∗
  (∀ ga gb, |==> P Init ga gb kA kB ∗ Q Init ga gb kA kB) -∗
  (∀ ogab : option term,
      (if ogab is Some gab then ∃ a gb,
         ⌜gab = Spec.texp gb a⌝ ∧
         sterm gab ∧
         Q Init (TExp g [a]) gb kA kB ∗
         (corruption kA kB ∨
          ∃ b, ⌜gb = TExp g [b]⌝ ∗
               P Resp (TExp g [a]) (TExp g [b]) kA kB ∗
               □ (pterm gab → ▷ False))
       else True) -∗
      Ψ (repr ogab)) -∗
  WP nsl_dh_init c g (TKey Dec kA) (TKey Enc kA) (TKey Enc kB) @ E {{ Ψ }}.
Proof.
iIntros (??) "#cP #ctx #s_g #p_e_kA #p_e_kB init Hpost".
rewrite /nsl_dh_init; wp_pures; wp_bind (mknonce _).
iApply (wp_mkdh (nsl_dh_fail kA) g).
iIntros (a) "#s_a #a_pred token".
rewrite (term_meta_token_difference _ (↑N.@"peer")); last solve_ndisj.
iDestruct "token" as "[dh token]".
iMod (term_meta_set _ _ kB with "dh") as "#dh"; eauto.
wp_pures; wp_bind (tgroup _); iApply wp_tgroup.
wp_pures; wp_bind (texp _ _); iApply wp_texp.
rewrite Spec.texpA; wp_pures; wp_bind (nsl_init _ _ _ _ _ _).
iApply (wp_nsl_init (nsl_dh_inv g) Q
          with "cP ctx p_e_kA p_e_kB [] [] [init] [token]") => //.
- solve_ndisj.
- rewrite sterm_TExp /=; iSplit => //.
  by rewrite /=; iSplit.
- by iModIntro; iApply pterm_nsl_dh1.
- iIntros (nB); rewrite /=.
  iMod ("init" $! (TExp g [a]) nB) as "[init resp]"; iModIntro.
  iFrame.
  iExists a; iSplit => //.
  iModIntro; iIntros (b) "p_b".
  by iApply pterm_nsl_dh2.
- rewrite (term_meta_token_difference _ (↑N.@"nsl")); last solve_ndisj.
  by iDestruct "token" as "[token _]".
iIntros (onB) "pub"; case: onB=> [nB|]; last by protocol_failure.
iDestruct "pub" as "[#s_nB [init [#fail | [resp #succ]]]]".
  wp_pures; wp_bind (texp _ _); iApply wp_texp; wp_pures.
  iApply ("Hpost" $! (Some (Spec.texp nB a))).
  iModIntro; iExists _, _; iSplit; eauto.
  iSplit; first by iApply sterm_texp => //.
  iFrame; by eauto.
iDestruct "succ" as (b) "(-> & #succ)".
wp_pures; wp_bind (texp _ _); iApply wp_texp; wp_pures.
iApply ("Hpost" $! (Some (Spec.texp (TExp g [b]) a))).
iModIntro; iExists _, _; iSplit => //.
iSplit; first by iApply sterm_texp => //.
iFrame.
iRight; iExists b.
rewrite Spec.texpA; iSplit => //; iFrame.
iIntros "!> #contra".
iDestruct ("succ" with "contra") as "{succ} >succ".
by iApply dh_seed_elim0.
Qed.

Lemma wp_nsl_dh_resp Q c γ g kB E Ψ :
  ↑cryptisN ⊆ E →
  ↑N ⊆ E →
  channel c -∗
  nsl_dh_ctx g γ -∗
  sterm g -∗
  pterm (TKey Enc kB) -∗
  (∀ ga gb kA, |==> P Resp ga gb kA kB ∗ Q Resp ga gb kA kB) -∗
  (∀ oresp : option (term * term),
      (if oresp is Some (pkA, gab) then
         ∃ kA b ga,
           ⌜pkA = TKey Enc kA⌝ ∧
           ⌜gab = Spec.texp ga b⌝ ∧
           pterm pkA ∧
           sterm gab ∧
           Q Resp ga (TExp g [b]) kA kB ∗
           (corruption kA kB ∨
            ∃ a, ⌜ga = TExp g [a]⌝ ∗
                  P Init ga (TExp g [b]) kA kB ∗
                  □ (pterm gab → ▷ False))
       else True) -∗
      Ψ (repr oresp)) -∗
  WP nsl_dh_resp c g (TKey Dec kB) (TKey Enc kB) @ E {{ Ψ }}.
Proof.
iIntros (??) "#? #ctx #s_g #p_e_kB resp Hpost".
rewrite /nsl_dh_resp; wp_pures; wp_bind (mkdh _).
iApply (wp_mkdh (nsl_dh_fail kB)).
iIntros (b) "#s_b #b_pred token".
rewrite (term_meta_token_difference _ (↑N.@"peer")); last solve_ndisj.
iDestruct "token" as "[dh token]".
wp_pures; wp_bind (tgroup _); iApply wp_tgroup.
wp_pures; wp_bind (texp _ _); iApply wp_texp.
rewrite Spec.texpA; wp_pures; wp_bind (nsl_resp _ _ _ _ _).
iApply (wp_nsl_resp (nsl_dh_inv g) Q 
          with "[//] ctx p_e_kB [token] [] [resp dh]") => //.
- solve_ndisj.
- rewrite (term_meta_token_difference _ (↑N.@"nsl")); last solve_ndisj.
  by iDestruct "token" as "[token _]".
- by rewrite sterm_TExp /=; iSplit; eauto.
- iIntros (kA nA).
  iMod (term_meta_set _ _ kA with "dh") as "#meta"; eauto.
  iMod ("resp" $! nA (TExp g [b]) kA) as "[resp init]".
  iModIntro; iSplit.
  + iModIntro; rewrite [corruption _ _]comm; by iApply pterm_nsl_dh1.
  + iFrame; iExists b; iSplit => //.
    iIntros "!> %".
    rewrite -[ [a; b]]/(seq.cat [a] [b]) TExpC /=.
    by iIntros "#?"; iApply pterm_nsl_dh2.
iIntros ([[pkA nA]|]) "resp"; last by protocol_failure.
iDestruct "resp" as (kA) "(-> & #p_e_kA & #s_nA & #p_nA & inv)".
wp_pures; wp_bind (texp _ _); iApply wp_texp; wp_pures.
iApply ("Hpost" $! (Some (TKey Enc kA, Spec.texp nA b))).
iModIntro; iExists _, _, _; do 4!iSplit => //; eauto.
  by iApply sterm_texp.
iDestruct "inv" as "[? inv]"; iFrame.
iDestruct "inv" as "[inv|[resp inv]]"; eauto.
iDestruct "inv" as (t) "[-> #inv]".
rewrite Spec.texpA.
rewrite -[ [b; t]]/(seq.cat [b] [t]) TExpC /=.
iRight; iExists _; iSplit => //; iFrame.
iIntros "!> #contra".
iSpecialize ("inv" with "contra").
iDestruct "inv" as ">inv".
by iApply dh_seed_elim0.
Qed.

End NSLDH.

Arguments nsl_dh_ctx {Σ _ _ _} N P g γ.
Arguments nsl_dh_alloc {Σ _ _ _} N P g E E'.
Arguments wp_nsl_dh_init {Σ _ _ _ N} P Q.
Arguments wp_nsl_dh_resp {Σ _ _ _ N} P Q.
