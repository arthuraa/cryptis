From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import mono_nat.
From iris.program_logic Require Export total_adequacy.
From iris.heap_lang Require Export adequacy.
From iris.heap_lang Require Import proofmode notation.
From iris.prelude Require Import options.
From cryptis.lib Require Import gen_adequacy.

Lemma heap_twp_rtc Σ `{!heapGpreS Σ} e es1 es2 σ φ :
  (∀ `{!heapGS_gen HasNoLc Σ}, ⊢ inv_heap_inv -∗ WP e [{ v, ⌜φ v⌝ }]) →
  ∃ v es' σ',
  rtc erased_step (es1 ++ e :: es2, σ) (es1 ++ of_val v :: es2 ++ es', σ') ∧
  φ v.
Proof.
  intros Hwp; eapply (twp_rtc _ _); iIntros (?) "".
  iMod (gen_heap_init σ.(heap)) as (?) "[Hh _]".
  iMod (inv_heap_init loc (option val)) as (?) ">Hi".
  iMod (proph_map_init [] σ.(used_proph_id)) as (?) "Hp".
  iMod (mono_nat_own_alloc 0) as (γ) "[Hsteps _]".
  iModIntro.
  iExists
    (λ σ ns κs _, (gen_heap_interp σ.(heap) ∗
                   proph_map_interp κs σ.(used_proph_id) ∗
                   mono_nat_auth_own γ 1 ns)%I),
    id, (λ _, True%I), _; iFrame.
  by iApply (Hwp (HeapGS _ _ _ _ _ _ _ _)).
Qed.
