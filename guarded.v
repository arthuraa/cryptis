From mathcomp Require Import ssreflect.
From iris.base_logic.lib Require Import auth.
From iris.base_logic Require Import proofmode.
From iris.proofmode Require Import tactics.
From iris_string_ident Require Import ltac2_string_ident.

Section Guarded.

Context `{Σ : gFunctors}.
Notation iProp := (iProp Σ).

Implicit Types (P Q : iProp) (G : Prop).

Definition guarded G `{Decision G} P : iProp :=
  (if decide G then P else emp)%I.

Lemma guarded_leq G1 G2 `{Decision G1, Decision G2} P :
  (G2 → G1) →
  guarded G1 P -∗ guarded G2 P.
Proof.
rewrite /guarded.
case: (decide G1) (decide G2) => [yes1|no1] [yes2|no2] //= H12;
iIntros "H //"; by case: (no1 (H12 yes2)).
Qed.

Context `{!Decision G}.

Global Instance guarded_persistent P :
  Persistent P →
  Persistent (guarded G P).
Proof. rewrite /guarded; case: decide => //= _; apply _. Qed.

Lemma guarded_sep P Q :
  guarded G (P ∗ Q) ⊣⊢ guarded G P ∗ guarded G Q.
Proof.
rewrite /guarded; case: decide => /=; eauto.
by rewrite -bi.intuitionistically_emp -bi.intuitionistically_sep_dup.
Qed.

Global Instance guarded_from_sep P Q R :
  FromSep P Q R →
  FromSep (guarded G P) (guarded G Q) (guarded G R).
Proof.
rewrite {2}/FromSep; iIntros (FS) "H".
rewrite -guarded_sep /guarded; case: decide => //= _.
by iApply from_sep.
Qed.

Global Instance guarded_into_sep P Q R :
  IntoSep P Q R →
  IntoSep (guarded G P) (guarded G Q) (guarded G R).
Proof.
rewrite {2}/IntoSep; iIntros (FS) "H".
rewrite -guarded_sep /guarded; case: decide => //= _.
by iApply into_sep.
Qed.

Global Instance guarded_into_and b (P Q R : iProp) :
  IntoAnd b P Q R →
  IntoAnd b (guarded G P) (guarded G Q) (guarded G R).
Proof.
rewrite /guarded.
by case: b (decide G) => [] //= [] _ //= _; rewrite /IntoAnd /=; eauto.
Qed.

Lemma guarded_fupd `{!invG Σ} E P :
  guarded G (|={E}=> P) ⊣⊢ |={E}=> guarded G P.
Proof.
rewrite /guarded.
by case: decide => //= _; apply (anti_symm _); iIntros => //.
Qed.

Lemma guarded_later P :
  guarded G (▷ P) ⊣⊢ ▷ guarded G P.
Proof.
rewrite /guarded.
by case: decide => //= _; rewrite bi.later_emp.
Qed.

Lemma guarded_mono P Q :
  guarded G P -∗
  □ (P -∗ Q) -∗
  guarded G Q.
Proof.
rewrite /guarded.
iIntros "HP #PQ"; by case: decide => // _; iApply "PQ".
Qed.

Lemma guarded_exist T (φ : T -> iProp) :
  Inhabited T →
  guarded G (∃ x : T, φ x) ⊣⊢ ∃ x : T, guarded G (φ x).
Proof.
rewrite /guarded.
move=> ?; case: decide=> //= _.
apply (anti_symm _); last by eauto.
by iIntros "_"; iExists inhabitant.
Qed.

Global Instance guarded_from_exist T (φ : T -> iProp) :
  Inhabited T →
  FromExist (guarded G (∃ x, φ x)) (λ x, guarded G (φ x)).
Proof.
by move => ?; rewrite /FromExist guarded_exist.
Qed.

Global Instance guarded_into_exist T (φ : T -> iProp) :
  Inhabited T →
  IntoExist (guarded G (∃ x, φ x)) (λ x, guarded G (φ x)).
Proof.
by move => ?; rewrite /IntoExist guarded_exist.
Qed.

Lemma guarded_box (P : iProp) : □ guarded G P ⊣⊢ guarded G (□ P).
Proof.
rewrite /guarded.
case: decide => //= _; by rewrite bi.intuitionistically_emp.
Qed.

Global Instance guarded_box_into_persistent p (P Q : iProp) :
  IntoPersistent p P Q →
  IntoPersistent p (guarded G P) (guarded G Q).
Proof.
rewrite /guarded.
case: decide => //= _ _.
by rewrite /IntoPersistent; rewrite -bi.persistently_emp_intro; eauto.
Qed.

End Guarded.
