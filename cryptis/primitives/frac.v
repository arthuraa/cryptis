(* HeapLang implementations of the operations of [cryptis.lib.frac] on
   canonical fractions, parameterised by HeapLang closures for the variables,
   as in [primitives/poly.v].  A fraction is represented by the pair of its
   numerator and denominator ([repr_frac]), so [frac_make] cancels with
   [poly_cancel], and equality is equality of the two components. *)

From mathcomp Require Import ssreflect.
From stdpp Require Import list.
From iris.heap_lang Require Import notation proofmode.
From cryptis.lib Require Import repr list mset sms poly poly_gcd frac.
From cryptis.primitives Require Import mset sms poly.

Unset Printing Implicit Defensive.

#[global] Instance repr_frac {T} `{!Repr T, EqDecision T, Lexico T}
  `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)} :
  Repr (Frac.frac T) := λ r, repr (Frac.num r, Frac.den r).

Lemma repr_fracE {T} `{!Repr T, EqDecision T, Lexico T}
    `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)}
    (r : Frac.frac T) :
  repr r = repr (Frac.num r, Frac.den r).
Proof. done. Qed.

(** ** Implementations *)

Definition frac_zero : val := (poly_zero, poly_one).

Definition frac_one : val := (poly_one, poly_one).

Definition frac_var : val := λ: "x", (poly_var "x", poly_one).

Definition frac_make : val := λ: "eq" "le" "p" "q",
  if: poly_eq "eq" "q" poly_zero then frac_zero
  else poly_cancel "eq" "le" "p" "q".

Definition frac_opp : val := λ: "f", (poly_opp (Fst "f"), Snd "f").

Definition frac_add : val := λ: "eq" "le" "f" "g",
  frac_make "eq" "le"
    (poly_add "eq" "le" (poly_mul "eq" "le" (Fst "f") (Snd "g"))
                        (poly_mul "eq" "le" (Fst "g") (Snd "f")))
    (poly_mul "eq" "le" (Snd "f") (Snd "g")).

Definition frac_mul : val := λ: "eq" "le" "f" "g",
  frac_make "eq" "le" (poly_mul "eq" "le" (Fst "f") (Fst "g"))
                      (poly_mul "eq" "le" (Snd "f") (Snd "g")).

Definition frac_inv : val := λ: "eq" "le" "f",
  frac_make "eq" "le" (Snd "f") (Fst "f").

Definition frac_eq : val := λ: "eq" "f" "g",
  poly_eq "eq" (Fst "f") (Fst "g") && poly_eq "eq" (Snd "f") (Snd "g").

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

Implicit Types (x : T) (p q : Poly.poly T) (f g : Frac.frac T).

#[local] Lemma repr_pairE p q : repr (p, q) = (repr p, repr q)%V.
Proof. done. Qed.

Lemma repr_poly_one : repr (Poly.one : Poly.poly T) = poly_one.
Proof.
rewrite Poly.oneE repr_polyE Poly.car_mono repr_smsE SMS.pos_singleton.
rewrite SMS.neg_singleton /repr_prod /= /repr_mset MSet.elements_singleton.
by rewrite MSet.elements_empty [@repr_list]unlock /= MSet.elements_empty.
Qed.

Lemma repr_frac_zero : repr (Frac.zero : Frac.frac T) = frac_zero.
Proof.
by rewrite repr_fracE Frac.num_zero Frac.den_zero repr_pairE repr_poly_zero
  repr_poly_one.
Qed.

Lemma repr_frac_one : repr (Frac.one : Frac.frac T) = frac_one.
Proof.
by rewrite repr_fracE Frac.num_one Frac.den_one repr_pairE repr_poly_one.
Qed.

Lemma twp_frac_zero E Ψ :
  Ψ (repr (Frac.zero : Frac.frac T)) ⊢ WP Val frac_zero @ E [{ Ψ }].
Proof. by rewrite repr_frac_zero; iIntros "HΨ"; wp_pures. Qed.

Lemma twp_frac_one E Ψ :
  Ψ (repr (Frac.one : Frac.frac T)) ⊢ WP Val frac_one @ E [{ Ψ }].
Proof. by rewrite repr_frac_one; iIntros "HΨ"; wp_pures. Qed.

Lemma twp_frac_var x E Ψ :
  Ψ (repr (Frac.var x)) ⊢ WP frac_var (repr x) @ E [{ Ψ }].
Proof.
rewrite repr_fracE Frac.varE Frac.num_of_poly Frac.den_of_poly.
rewrite repr_pairE repr_poly_one.
iIntros "HΨ"; wp_lam; wp_apply twp_poly_var; wp_pures.
by iApply "HΨ".
Qed.

Lemma twp_frac_make p q E Ψ :
  Ψ (repr (Frac.make p q)) ⊢
  WP frac_make eqv lev (repr p) (repr q) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam; wp_pures; rewrite -repr_poly_zero.
wp_apply (twp_poly_eq eqv eqvP).
case: bool_decide_reflect => [->|nq]; wp_pures.
  by rewrite Frac.make_den0 repr_frac_zero.
wp_apply (twp_poly_cancel eqv lev eqvP levP).
have [en ed] := Frac.make_cancel p q nq.
by rewrite repr_fracE en ed; case: (Poly.cancel p q).
Qed.

Lemma twp_frac_opp f E Ψ :
  Ψ (repr (Frac.opp f)) ⊢ WP frac_opp (repr f) @ E [{ Ψ }].
Proof.
rewrite !repr_fracE Frac.num_opp Frac.den_opp !repr_pairE.
iIntros "HΨ"; wp_lam; wp_pures; wp_apply twp_poly_opp; wp_pures.
by iApply "HΨ".
Qed.

Lemma twp_frac_add f g E Ψ :
  Ψ (repr (Frac.add f g)) ⊢
  WP frac_add eqv lev (repr f) (repr g) @ E [{ Ψ }].
Proof.
rewrite Frac.addE [repr f]repr_fracE [repr g]repr_fracE !repr_pairE.
iIntros "HΨ"; wp_lam; wp_pures.
wp_apply (twp_poly_mul eqv lev eqvP levP); wp_pures.
wp_apply (twp_poly_mul eqv lev eqvP levP); wp_pures.
wp_apply (twp_poly_mul eqv lev eqvP levP).
wp_apply (twp_poly_add eqv lev eqvP levP).
by wp_apply twp_frac_make.
Qed.

Lemma twp_frac_mul f g E Ψ :
  Ψ (repr (Frac.mul f g)) ⊢
  WP frac_mul eqv lev (repr f) (repr g) @ E [{ Ψ }].
Proof.
rewrite Frac.mulE [repr f]repr_fracE [repr g]repr_fracE !repr_pairE.
iIntros "HΨ"; wp_lam; wp_pures.
wp_apply (twp_poly_mul eqv lev eqvP levP); wp_pures.
wp_apply (twp_poly_mul eqv lev eqvP levP).
by wp_apply twp_frac_make.
Qed.

Lemma twp_frac_inv f E Ψ :
  Ψ (repr (Frac.inv f)) ⊢ WP frac_inv eqv lev (repr f) @ E [{ Ψ }].
Proof.
rewrite Frac.invE [repr f]repr_fracE repr_pairE.
by iIntros "HΨ"; wp_lam; wp_pures; wp_apply twp_frac_make.
Qed.

Lemma twp_frac_eq f g E Ψ :
  Ψ #(bool_decide (f = g)) ⊢ WP frac_eq eqv (repr f) (repr g) @ E [{ Ψ }].
Proof.
have -> : bool_decide (f = g) =
          bool_decide (Frac.num f = Frac.num g) &&
          bool_decide (Frac.den f = Frac.den g).
  rewrite -bool_decide_and; apply: bool_decide_ext.
  by split=> [->|[]]; [|exact: Frac.num_den_inj].
rewrite !repr_fracE !repr_pairE.
iIntros "HΨ"; wp_lam; wp_pures.
wp_apply (twp_poly_eq eqv eqvP).
case: bool_decide; wp_pures; last by iApply "HΨ".
by wp_apply (twp_poly_eq eqv eqvP).
Qed.

End Proofs.
