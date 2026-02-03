(* From stdpp Require Import base gmap. *)
From mathcomp Require Import ssreflect.
(* From stdpp Require Import namespaces. *)
(* From iris.algebra Require Import agree auth csum gset gmap excl frac. *)
(* From iris.algebra Require Import numbers reservation_map. *)
From iris.heap_lang Require Import notation proofmode adequacy.
(* From iris.heap_lang.lib Require Import par assert ticket_lock. *)
From cryptis Require Import lib cryptis primitives tactics.
From cryptis.primitives Require Import attacker.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma cryptis_adequacy `{!heapGpreS Σ, cryptisGpreS Σ} (f : val heap_lang) σ φ :
  (∀ `{!heapGS Σ, !cryptisGS Σ} c,
      cryptis_ctx -∗
      channel c -∗
      seal_pred_token AENC ⊤ ∗
      seal_pred_token SIGN ⊤ ∗
      seal_pred_token SENC ⊤ ∗
      hash_pred_token ⊤ -∗
      WP f c {{ v, ⌜φ v⌝ }}) →
  adequate NotStuck (run_network f) σ (λ v _, φ v).
Proof.
move=> wp_f; apply: heap_adequacy.
iIntros (Hheap) "_".
iMod cryptisGS_alloc as (Hcryptis) "(#? & aenc & sign & senc & hash)".
wp_apply (wp_run_network with "[aenc sign senc hash]") => //.
iIntros (c) "_ #chan". by wp_apply (wp_f with "[] [] [$]").
Qed.
