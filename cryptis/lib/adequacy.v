From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import mono_nat.
From iris.program_logic Require Export total_adequacy.
From iris.heap_lang Require Export adequacy.
From iris.heap_lang Require Import proofmode notation.
From iris.prelude Require Import options.
From cryptis Require Import lib.
From cryptis.lib Require Import gen_adequacy.

Lemma heap_twp_thread_exec Σ `{!heapGpreS Σ} e σ φ :
  (∀ `{!heapGS Σ}, ⊢ inv_heap_inv -∗ WP e [{ v, ⌜φ v⌝ }]) →
  ∃ v σ', rtc thread_step (e, σ) (of_val v, σ') ∧ φ v.
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

Lemma thread_exec_pure_exec (e : expr) σ e' σ' :
  rtc thread_step (e, σ) (e', σ') →
  pure_expr e →
  rtc pure_step e e'.
Proof.
set t := (e, σ); set t' := (e', σ').
rewrite -[e]/(t.1) -[e']/(t'.1); move: t t' => t t' {e σ e' σ'}.
elim: t t' / => //= - [e σ] [e' σ'] [e'' σ''] [/= efs Hstep] _ IH pure_e.
have pure_e' : pure_expr e' by apply: pure_exprP.
have {}Hstep : pure_step e e' by apply: pure_expr_pure_step.
by apply: rtc_l; eauto.
Qed.

Lemma heap_twp_pure_exec Σ `{!heapGpreS Σ} e φ :
  pure_expr e →
  (∀ `{!heapGS Σ}, ⊢ inv_heap_inv -∗ WP e [{ v, ⌜φ v⌝ }]) →
  ∃ v, rtc pure_step e (of_val v) ∧ φ v.
Proof.
move=> pure_e /heap_twp_thread_exec Hwp.
have [v [] σ' [] Hexec post] := Hwp {| heap := ∅; used_proph_id := ∅ |}.
exists v; split => //.
exact: thread_exec_pure_exec Hexec pure_e.
Qed.
