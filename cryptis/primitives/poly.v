(* HeapLang implementations of the polynomial operations of [cryptis.lib.poly],
   parameterised by HeapLang closures for the variables, as in
   [primitives/mset.v]: an equality test [eq] and a test [le] for [MSet.le].
   A polynomial is represented by its signed multiset of monomials
   ([repr_poly]), and its operations are those of [primitives/sms.v] on
   monomials, which are compared with [mset_eq] and [mset_le].  The specs are
   continuation-style, like those of [primitives/sms.v]. *)

From mathcomp Require Import ssreflect.
From stdpp Require Import list.
From iris.heap_lang Require Import notation proofmode.
From cryptis.lib Require Import repr list mset sms poly.
From cryptis.primitives Require Import mset sms.

Unset Printing Implicit Defensive.

#[global] Instance repr_poly {T} `{!Repr T, EqDecision T, Lexico T}
  `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)} :
  Repr (Poly.poly T) := λ p, repr (Poly.car p).

Lemma repr_polyE {T} `{!Repr T, EqDecision T, Lexico T}
    `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)}
    (p : Poly.poly T) :
  repr p = repr (Poly.car p).
Proof. done. Qed.

(** ** Implementations *)

Definition poly_coeff : val := λ: "eq" "m" "p",
  let: "meq" := λ: "X" "Y", mset_eq "eq" "X" "Y" in
  sms_count "meq" "m" "p".

Definition poly_mono : val := λ: "m", ("m" :: NILV, NILV).

Definition poly_zero : val := (NILV, NILV).

Definition poly_one : val := (CONSV NILV NILV, NILV).

Definition poly_var : val := λ: "x", poly_mono ("x" :: NILV).

Definition poly_add : val := λ: "eq" "le" "p" "q",
  let: "meq" := λ: "X" "Y", mset_eq "eq" "X" "Y" in
  let: "mle" := λ: "X" "Y", mset_le "eq" "le" "X" "Y" in
  sms_disj_union "meq" "mle" "p" "q".

Definition poly_opp : val := λ: "p", sms_inv "p".

Definition poly_mul : val := λ: "eq" "le" "p" "q",
  let: "meq" := λ: "X" "Y", mset_eq "eq" "X" "Y" in
  let: "mle" := λ: "X" "Y", mset_le "eq" "le" "X" "Y" in
  sms_bind "meq" "mle"
    (λ: "m", sms_map "meq" "mle" (λ: "n", mset_disj_union "le" "m" "n") "q")
    "p".

(** ** Specifications *)

Section Proofs.

Context `{!heapGS Σ}.
Context {T : Type} `{!Repr T, EqDecision T, Lexico T}
  `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)}.
Context (eqv lev : val).
Hypothesis eqvP : ∀ (x y : T) E Ψ,
  Ψ #(bool_decide (x = y)) ⊢ WP eqv (repr x) (repr y) @ E [{ Ψ }].
Hypothesis levP : ∀ (x y : T) E Ψ,
  Ψ #(bool_decide (MSet.le x y)) ⊢ WP lev (repr x) (repr y) @ E [{ Ψ }].

Implicit Types (x : T) (m n : MSet.mset T) (p q : Poly.poly T).

#[local] Lemma meqP m n E Ψ :
  Ψ #(bool_decide (m = n)) ⊢
  WP (λ: "X" "Y", mset_eq eqv "X" "Y")%V (repr m) (repr n) @ E [{ Ψ }].
Proof. iIntros "HΨ"; wp_pures; by wp_apply (twp_mset_eq eqv eqvP). Qed.

#[local] Lemma mleP m n E Ψ :
  Ψ #(bool_decide (MSet.le m n)) ⊢
  WP (λ: "X" "Y", mset_le eqv lev "X" "Y")%V (repr m) (repr n) @ E [{ Ψ }].
Proof. iIntros "HΨ"; wp_pures; by wp_apply (twp_mset_le eqv lev eqvP levP). Qed.

Lemma twp_poly_coeff m p E Ψ :
  Ψ #(Poly.coeff m p) ⊢ WP poly_coeff eqv (repr m) (repr p) @ E [{ Ψ }].
Proof.
rewrite repr_polyE; iIntros "HΨ"; wp_lam; wp_pures.
by wp_apply (twp_sms_count _ meqP).
Qed.

Lemma twp_poly_mono m E Ψ :
  Ψ (repr (Poly.mono m)) ⊢ WP poly_mono (repr m) @ E [{ Ψ }].
Proof.
have -> : repr (Poly.mono m) = (SOMEV (repr m, NONEV), NONEV)%V.
  by rewrite repr_polyE repr_smsE /repr_prod /= /repr_mset [@repr_list]unlock.
iIntros "HΨ"; wp_lam; rewrite /CONS; wp_pures.
by iApply "HΨ".
Qed.

Lemma twp_poly_zero E Ψ :
  Ψ (repr (Poly.zero : Poly.poly T)) ⊢ WP Val poly_zero @ E [{ Ψ }].
Proof.
have -> : repr (Poly.zero : Poly.poly T) = poly_zero.
  by rewrite repr_polyE repr_smsE /repr_prod /= /repr_mset [@repr_list]unlock.
by iIntros "HΨ"; wp_pures.
Qed.

Lemma twp_poly_one E Ψ :
  Ψ (repr (Poly.one : Poly.poly T)) ⊢ WP Val poly_one @ E [{ Ψ }].
Proof.
have -> : repr (Poly.one : Poly.poly T) = poly_one.
  by rewrite repr_polyE repr_smsE /repr_prod /= /repr_mset [@repr_list]unlock.
by iIntros "HΨ"; wp_pures.
Qed.

Lemma twp_poly_var x E Ψ :
  Ψ (repr (Poly.var x)) ⊢ WP poly_var (repr x) @ E [{ Ψ }].
Proof.
have e : SOMEV (repr x, NONEV)%V = repr ({[+ x +]} : MSet.mset T).
  by rewrite /repr_mset [@repr_list]unlock.
iIntros "HΨ"; wp_lam; rewrite /CONS; wp_pures; rewrite e.
by wp_apply twp_poly_mono.
Qed.

Lemma twp_poly_add p q E Ψ :
  Ψ (repr (Poly.add p q)) ⊢
  WP poly_add eqv lev (repr p) (repr q) @ E [{ Ψ }].
Proof.
rewrite !repr_polyE; iIntros "HΨ"; wp_lam; wp_pures.
by wp_apply (twp_sms_disj_union _ _ meqP mleP).
Qed.

Lemma twp_poly_opp p E Ψ :
  Ψ (repr (Poly.opp p)) ⊢ WP poly_opp (repr p) @ E [{ Ψ }].
Proof. rewrite !repr_polyE; iIntros "HΨ"; wp_lam; by wp_apply twp_sms_inv. Qed.

Lemma twp_poly_mul p q E Ψ :
  Ψ (repr (Poly.mul p q)) ⊢
  WP poly_mul eqv lev (repr p) (repr q) @ E [{ Ψ }].
Proof.
rewrite !repr_polyE; iIntros "HΨ"; wp_lam; wp_pures.
wp_apply (twp_sms_bind _ _ meqP mleP
            (λ m, SMS.map (λ n, m ⊎ n) (Poly.car q))) => //.
move=> m E' Φ; iIntros "HΦ"; wp_pures.
wp_apply (twp_sms_map _ _ meqP mleP (λ n, m ⊎ n)) => //.
move=> n E'' Φ'; iIntros "HΦ'"; wp_pures.
by wp_apply (twp_mset_disj_union lev levP).
Qed.

End Proofs.
