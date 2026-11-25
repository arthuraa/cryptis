(* HeapLang implementations of the polynomial operations of [cryptis.lib.poly],
   parameterised by HeapLang closures for the variables, as in
   [primitives/mset.v]: an equality test [eq] and a test [le] for [MSet.le].
   A polynomial is represented by its signed multiset of monomials
   ([repr_poly]), and its operations are those of [primitives/sms.v] on
   monomials, which are compared with [mset_eq] and [mset_le].  The specs are
   continuation-style, like those of [primitives/sms.v].

   [poly_gcd], [poly_div] and [poly_cancel] follow [Poly.ops]: [poly_gcd_vs]
   and [poly_div_vs] recur on the list of variables, and pass the operations
   of the level below to [poly_gcd_lvl] and [poly_div_lvl] as closures, whose
   specs are the hypotheses of section [Level]. *)

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

Definition poly_eq : val := λ: "eq" "p" "q",
  let: "meq" := λ: "X" "Y", mset_eq "eq" "X" "Y" in
  sms_eq "meq" "p" "q".

Definition poly_const : val := λ: "eq" "le" "n",
  let: "meq" := λ: "X" "Y", mset_eq "eq" "X" "Y" in
  let: "mle" := λ: "X" "Y", mset_le "eq" "le" "X" "Y" in
  sms_to "meq" (mset_of_list "mle" (replicate_list "n" NILV))
    (mset_of_list "mle" (replicate_list (- "n") NILV)).

Definition poly_sub : val := λ: "eq" "le" "p" "q",
  poly_add "eq" "le" "p" (poly_opp "q").

Definition poly_vpow : val := λ: "le" "x" "k",
  mset_of_list "le" (replicate_list "k" "x").

Definition poly_deg : val := λ: "eq" "x" "p",
  foldr_list
    (λ: "m" "n",
       let: "c" := mset_count "eq" "x" "m" in if: "n" < "c" then "c" else "n")
    #0 (append_lists (Fst "p") (Snd "p")).

Definition poly_coeffx : val := λ: "eq" "le" "x" "k" "p",
  let: "meq" := λ: "X" "Y", mset_eq "eq" "X" "Y" in
  let: "mle" := λ: "X" "Y", mset_le "eq" "le" "X" "Y" in
  let: "xk" := poly_vpow "le" "x" "k" in
  sms_bind "meq" "mle"
    (λ: "m", if: mset_count "eq" "x" "m" = "k"
             then poly_mono (mset_difference "eq" "m" "xk") else poly_zero)
    "p".

Definition poly_lcx : val := λ: "eq" "le" "x" "p",
  poly_coeffx "eq" "le" "x" (poly_deg "eq" "x" "p") "p".

Definition poly_vars : val := λ: "eq" "p",
  remove_dups_list "eq"
    (foldr_list append_lists NILV (append_lists (Fst "p") (Snd "p"))).

Definition poly_prem_loop : val :=
  rec: "loop" "eq" "le" "x" "b" "d" "l" "fuel" "r" :=
  if: "fuel" = #0 then "r" else
  if: poly_eq "eq" "r" poly_zero || (poly_deg "eq" "x" "r" < "d")
  then "r" else
  let: "k" := poly_deg "eq" "x" "r" - "d" in
  let: "t" := poly_mul "eq" "le" (poly_lcx "eq" "le" "x" "r")
                (poly_mono (poly_vpow "le" "x" "k")) in
  "loop" "eq" "le" "x" "b" "d" "l" ("fuel" - #1)
    (poly_sub "eq" "le" (poly_mul "eq" "le" "l" "r")
       (poly_mul "eq" "le" "t" "b")).

Definition poly_prem : val := λ: "eq" "le" "x" "a" "b",
  poly_prem_loop "eq" "le" "x" "b" (poly_deg "eq" "x" "b")
    (poly_lcx "eq" "le" "x" "b") (poly_deg "eq" "x" "a" + #1) "a".

Definition poly_div_loop : val :=
  rec: "loop" "eq" "le" "dv" "x" "g" "d" "l" "fuel" "r" "q" :=
  if: "fuel" = #0 then "q" else
  if: poly_eq "eq" "r" poly_zero then "q" else
  let: "k" := poly_deg "eq" "x" "r" - "d" in
  let: "c" := poly_mul "eq" "le" ("dv" (poly_lcx "eq" "le" "x" "r") "l")
                (poly_mono (poly_vpow "le" "x" "k")) in
  "loop" "eq" "le" "dv" "x" "g" "d" "l" ("fuel" - #1)
    (poly_sub "eq" "le" "r" (poly_mul "eq" "le" "c" "g"))
    (poly_add "eq" "le" "q" "c").

Definition poly_div_lvl : val := λ: "eq" "le" "dv" "x" "p" "g",
  poly_div_loop "eq" "le" "dv" "x" "g" (poly_deg "eq" "x" "g")
    (poly_lcx "eq" "le" "x" "g") (poly_deg "eq" "x" "p" + #1) "p" poly_zero.

Definition poly_cont_loop : val :=
  rec: "loop" "eq" "le" "gc" "x" "p" "i" "n" :=
  if: "n" = #0 then poly_zero else
  "gc" (poly_coeffx "eq" "le" "x" "i" "p")
    ("loop" "eq" "le" "gc" "x" "p" ("i" + #1) ("n" - #1)).

Definition poly_cont : val := λ: "eq" "le" "gc" "x" "p",
  poly_cont_loop "eq" "le" "gc" "x" "p" #0 (poly_deg "eq" "x" "p" + #1).

Definition poly_prs : val :=
  rec: "loop" "eq" "le" "gc" "dv" "x" "fuel" "a" "b" :=
  if: "fuel" = #0 then "a" else
  if: poly_eq "eq" "b" poly_zero then "a" else
  let: "r" := poly_prem "eq" "le" "x" "a" "b" in
  "loop" "eq" "le" "gc" "dv" "x" ("fuel" - #1) "b"
    (poly_div_lvl "eq" "le" "dv" "x" "r" (poly_cont "eq" "le" "gc" "x" "r")).

Definition poly_gcd_lvl : val := λ: "eq" "le" "gc" "dv" "x" "p" "q",
  if: poly_eq "eq" "p" poly_zero then "q" else
  if: poly_eq "eq" "q" poly_zero then "p" else
  let: "cp" := poly_cont "eq" "le" "gc" "x" "p" in
  let: "cq" := poly_cont "eq" "le" "gc" "x" "q" in
  let: "a" := poly_div_lvl "eq" "le" "dv" "x" "p" "cp" in
  let: "b" := poly_div_lvl "eq" "le" "dv" "x" "q" "cq" in
  let: "da" := poly_deg "eq" "x" "a" in
  let: "db" := poly_deg "eq" "x" "b" in
  let: "g" :=
    if: "da" < "db" then poly_prs "eq" "le" "gc" "dv" "x" ("da" + #2) "b" "a"
    else poly_prs "eq" "le" "gc" "dv" "x" ("db" + #2) "a" "b" in
  poly_mul "eq" "le" ("gc" "cp" "cq") "g".

Definition int_gcd : val := rec: "loop" "a" "b" :=
  if: "b" = #0 then (if: "a" < #0 then - "a" else "a")
  else "loop" "b" ("a" `rem` "b").

Definition poly_div_vs : val := rec: "loop" "eq" "le" "vs" "p" "q" :=
  match: "vs" with
    NONE =>
      poly_const "eq" "le"
        (poly_coeff "eq" NILV "p" `quot` poly_coeff "eq" NILV "q")
  | SOME "c" =>
      poly_div_lvl "eq" "le" (λ: "a" "b", "loop" "eq" "le" (Snd "c") "a" "b")
        (Fst "c") "p" "q"
  end.

Definition poly_gcd_vs : val := rec: "loop" "eq" "le" "vs" "p" "q" :=
  match: "vs" with
    NONE =>
      poly_const "eq" "le"
        (int_gcd (poly_coeff "eq" NILV "p") (poly_coeff "eq" NILV "q"))
  | SOME "c" =>
      poly_gcd_lvl "eq" "le" (λ: "a" "b", "loop" "eq" "le" (Snd "c") "a" "b")
        (λ: "a" "b", poly_div_vs "eq" "le" (Snd "c") "a" "b") (Fst "c") "p" "q"
  end.

Definition poly_gcd : val := λ: "eq" "le" "p" "q",
  let: "vs" := remove_dups_list "eq"
                 (append_lists (poly_vars "eq" "p") (poly_vars "eq" "q")) in
  poly_gcd_vs "eq" "le" "vs" "p" "q".

Definition poly_div : val := λ: "eq" "le" "p" "q",
  let: "vs" := remove_dups_list "eq"
                 (append_lists (poly_vars "eq" "p") (poly_vars "eq" "q")) in
  poly_div_vs "eq" "le" "vs" "p" "q".

Definition poly_first_neg : val := λ: "eq" "le" "p",
  let: "mle" := λ: "X" "Y", mset_le "eq" "le" "X" "Y" in
  match: mset_disj_union "mle" (Fst "p") (Snd "p") with
    NONE => #false
  | SOME "c" => poly_coeff "eq" (Fst "c") "p" < #0
  end.

Definition poly_cancel_with : val := λ: "eq" "le" "g" "p" "q" "p'" "q'",
  if: poly_eq "eq" (poly_mul "eq" "le" "g" "p'") "p" &&
      poly_eq "eq" (poly_mul "eq" "le" "g" "q'") "q" then
    if: poly_first_neg "eq" "le" "q'" then (poly_opp "p'", poly_opp "q'")
    else ("p'", "q'")
  else ("p", "q").

Definition poly_cancel : val := λ: "eq" "le" "p" "q",
  let: "g" := poly_gcd "eq" "le" "p" "q" in
  poly_cancel_with "eq" "le" "g" "p" "q"
    (poly_div "eq" "le" "p" "g") (poly_div "eq" "le" "q" "g").

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

Lemma repr_poly_zero : repr (Poly.zero : Poly.poly T) = poly_zero.
Proof.
by rewrite repr_polyE repr_smsE /repr_prod /= /repr_mset [@repr_list]unlock.
Qed.

Lemma twp_poly_zero E Ψ :
  Ψ (repr (Poly.zero : Poly.poly T)) ⊢ WP Val poly_zero @ E [{ Ψ }].
Proof. by rewrite repr_poly_zero; iIntros "HΨ"; wp_pures. Qed.

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

Lemma twp_poly_eq p q E Ψ :
  Ψ #(bool_decide (p = q)) ⊢ WP poly_eq eqv (repr p) (repr q) @ E [{ Ψ }].
Proof.
have -> : bool_decide (p = q) = bool_decide (Poly.car p = Poly.car q).
  by apply: bool_decide_ext; split=> [->|/Poly.car_inj].
rewrite !repr_polyE; iIntros "HΨ"; wp_lam; wp_pures.
by wp_apply (twp_sms_eq _ meqP).
Qed.

Lemma twp_poly_const z E Ψ :
  Ψ (repr (Poly.const z : Poly.poly T)) ⊢
  WP poly_const eqv lev #z @ E [{ Ψ }].
Proof.
have eN : NILV = repr (∅ : MSet.mset T).
  by rewrite /repr_mset /= [@repr_list]unlock.
rewrite repr_polyE; iIntros "HΨ"; wp_lam; wp_pures; rewrite eN.
wp_apply (twp_replicate_list _ _ (∅ : MSet.mset T)).
wp_apply (twp_mset_of_list _ mleP).
wp_apply (twp_replicate_list _ _ (∅ : MSet.mset T)).
wp_apply (twp_mset_of_list _ mleP).
by wp_apply (twp_sms_to _ meqP).
Qed.

Lemma twp_poly_sub p q E Ψ :
  Ψ (repr (Poly.sub p q)) ⊢
  WP poly_sub eqv lev (repr p) (repr q) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam; wp_pures; wp_apply twp_poly_opp.
by wp_apply twp_poly_add.
Qed.

Lemma twp_poly_vpow x (k : Z) E Ψ :
  Ψ (repr (Poly.vpow x (Z.to_nat k))) ⊢
  WP poly_vpow lev (repr x) #k @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam; wp_pures; wp_apply (twp_replicate_list _ _ x).
by wp_apply (twp_mset_of_list lev levP).
Qed.

Lemma twp_poly_deg x p E Ψ :
  Ψ #(Poly.deg x p) ⊢ WP poly_deg eqv (repr x) (repr p) @ E [{ Ψ }].
Proof.
set f := λ m (z : Z),
  if bool_decide (z < MSet.count x m)%Z then Z.of_nat (MSet.count x m) else z.
have e l : foldr f 0%Z l = Z.of_nat (max_list (MSet.count x <$> l)).
  elim: l => [|m l IH] //=; rewrite IH /f; set k := max_list _.
  case_bool_decide; lia.
rewrite /Poly.deg -e repr_polyE [repr (Poly.car p)]repr_smsE /repr_prod /=.
iIntros "HΨ"; wp_lam; wp_pures; wp_apply twp_append_lists; wp_pures.
wp_apply (twp_foldr_list f _ _ 0%Z) => //.
  iIntros "%m %z %Φ _ HΦ"; wp_pures; wp_apply (twp_mset_count eqv eqvP).
  by wp_pures; rewrite /f; case_bool_decide; wp_pures; iApply "HΦ".
by iIntros "_".
Qed.

Lemma twp_poly_coeffx x (k : nat) p E Ψ :
  Ψ (repr (Poly.coeffx x k p)) ⊢
  WP poly_coeffx eqv lev (repr x) #k (repr p) @ E [{ Ψ }].
Proof.
rewrite !repr_polyE; iIntros "HΨ"; wp_lam; wp_pures.
wp_apply (twp_poly_vpow x (Z.of_nat k)); rewrite Nat2Z.id; wp_pures.
wp_apply (twp_sms_bind _ _ meqP mleP
            (λ m, if bool_decide (MSet.count x m = k)
                  then {[+ m ∖ Poly.vpow x k +]} else ∅)) => //.
move=> m E' Φ; iIntros "HΦ"; wp_pures.
wp_apply (twp_mset_count eqv eqvP); wp_pures.
rewrite [bool_decide (LitV _ = _)](bool_decide_ext _ (MSet.count x m = k)).
  case: bool_decide; wp_pures.
    wp_apply (twp_mset_difference eqv eqvP).
    by wp_apply twp_poly_mono.
  by rewrite -repr_poly_zero; iApply "HΦ".
by split=> [[/Nat2Z.inj]|->].
Qed.

Lemma twp_poly_lcx x p E Ψ :
  Ψ (repr (Poly.lcx x p)) ⊢
  WP poly_lcx eqv lev (repr x) (repr p) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam; wp_pures; wp_apply twp_poly_deg.
by wp_apply twp_poly_coeffx.
Qed.

Lemma twp_poly_vars p E Ψ :
  Ψ (repr (Poly.vars p)) ⊢ WP poly_vars eqv (repr p) @ E [{ Ψ }].
Proof.
have eN : NILV = repr ([] : list T) by rewrite repr_listE.
set f := λ (m : MSet.mset T) l, elements m ++ l.
have eb ms : foldr f [] ms = ms ≫= elements by elim: ms => //= m ms ->.
rewrite /Poly.vars -eb repr_polyE [repr (Poly.car p)]repr_smsE /repr_prod /=.
iIntros "HΨ"; wp_lam; wp_pures; rewrite eN.
wp_apply twp_append_lists.
wp_apply (twp_foldr_list f _ _ []) => //.
  iIntros "%m %l %Φ _ HΦ"; rewrite repr_msetE; wp_apply twp_append_lists.
  by iApply "HΦ".
iIntros "_"; wp_apply (twp_remove_dups_list eqv) => //.
  by iIntros "%a %b %Φ _ HΦ"; wp_apply eqvP; iApply "HΦ".
by iIntros "_".
Qed.

Lemma twp_poly_prem_loop x b (d : nat) l (fuel : nat) r E Ψ :
  Ψ (repr (Poly.prem_loop x b d l fuel r)) ⊢
  WP poly_prem_loop eqv lev (repr x) (repr b) #d (repr l) #fuel (repr r)
    @ E [{ Ψ }].
Proof.
elim: fuel r Ψ => [|fuel IH] r Ψ; iIntros "HΨ"; wp_rec; wp_pures.
  by iApply "HΨ".
rewrite -repr_poly_zero; wp_apply twp_poly_eq.
rewrite /=; case: bool_decide; wp_pures; first by iApply "HΨ".
wp_apply twp_poly_deg; wp_pures.
case: (Nat.ltb_spec (Poly.deg x r) d) => [lt|ge].
  by rewrite bool_decide_eq_true_2; [wp_pures; iApply "HΨ"|lia].
rewrite bool_decide_eq_false_2; last lia.
wp_pures; wp_apply twp_poly_deg; wp_pures.
wp_apply twp_poly_vpow; wp_apply twp_poly_mono; wp_apply twp_poly_lcx.
wp_apply twp_poly_mul; wp_pures.
wp_apply twp_poly_mul; wp_apply twp_poly_mul; wp_apply twp_poly_sub; wp_pures.
rewrite (_ : (S fuel - 1)%Z = fuel); last lia.
rewrite (_ : Z.to_nat (Poly.deg x r - d) = (Poly.deg x r - d)%nat); last lia.
by wp_apply IH.
Qed.

Lemma twp_poly_prem x a b E Ψ :
  Ψ (repr (Poly.prem x a b)) ⊢
  WP poly_prem eqv lev (repr x) (repr a) (repr b) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam; wp_pures; wp_apply twp_poly_deg; wp_pures.
wp_apply twp_poly_lcx; wp_apply twp_poly_deg.
rewrite (_ : (Poly.deg x a + 1)%Z = Z.of_nat (Poly.deg x a + 1)); last lia.
by wp_apply twp_poly_prem_loop.
Qed.

(** The operations of one level of [Poly.ops], given those of the level
    below. *)

Section Level.

Context (gc dv : Poly.poly T → Poly.poly T → Poly.poly T) (gcv dvv : val).
Hypothesis gcP : ∀ p q E Ψ,
  Ψ (repr (gc p q)) ⊢ WP gcv (repr p) (repr q) @ E [{ Ψ }].
Hypothesis dvP : ∀ p q E Ψ,
  Ψ (repr (dv p q)) ⊢ WP dvv (repr p) (repr q) @ E [{ Ψ }].

Lemma twp_poly_div_loop x g (d : nat) l (fuel : nat) r q E Ψ :
  Ψ (repr (Poly.div_loop x dv g d l fuel r q)) ⊢
  WP poly_div_loop eqv lev dvv (repr x) (repr g) #d (repr l) #fuel (repr r)
     (repr q) @ E [{ Ψ }].
Proof.
elim: fuel r q Ψ => [|fuel IH] r q Ψ; iIntros "HΨ"; wp_rec; wp_pures.
  by iApply "HΨ".
rewrite -repr_poly_zero; wp_apply twp_poly_eq.
rewrite /=; case: bool_decide; wp_pures; first by iApply "HΨ".
wp_apply twp_poly_deg; wp_pures.
wp_apply twp_poly_vpow; wp_apply twp_poly_mono; wp_apply twp_poly_lcx.
wp_apply dvP; wp_apply twp_poly_mul; wp_pures.
wp_apply twp_poly_add; wp_apply twp_poly_mul; wp_apply twp_poly_sub; wp_pures.
rewrite (_ : (S fuel - 1)%Z = fuel); last lia.
rewrite (_ : Z.to_nat (Poly.deg x r - d) = (Poly.deg x r - d)%nat); last lia.
by wp_apply IH.
Qed.

Lemma twp_poly_div_lvl x p g E Ψ :
  Ψ (repr (Poly.div_lvl x dv p g)) ⊢
  WP poly_div_lvl eqv lev dvv (repr x) (repr p) (repr g) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam; wp_pures; rewrite -repr_poly_zero.
wp_apply twp_poly_deg; wp_pures; wp_apply twp_poly_lcx; wp_apply twp_poly_deg.
rewrite (_ : (Poly.deg x p + 1)%Z = Z.of_nat (Poly.deg x p + 1)); last lia.
by wp_apply twp_poly_div_loop.
Qed.

Lemma twp_poly_cont_loop x p (i n : nat) E Ψ :
  Ψ (repr (foldr gc Poly.zero ((λ k, Poly.coeffx x k p) <$> seq i n))) ⊢
  WP poly_cont_loop eqv lev gcv (repr x) (repr p) #i #n @ E [{ Ψ }].
Proof.
elim: n i Ψ => [|n IH] i Ψ; iIntros "HΨ"; wp_rec; wp_pures.
  by rewrite -repr_poly_zero; iApply "HΨ".
rewrite (_ : (S n - 1)%Z = n); last lia.
rewrite (_ : (i + 1)%Z = S i); last lia.
wp_apply IH; wp_apply twp_poly_coeffx.
by wp_apply gcP.
Qed.

Lemma twp_poly_cont x p E Ψ :
  Ψ (repr (Poly.cont x gc p)) ⊢
  WP poly_cont eqv lev gcv (repr x) (repr p) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam; wp_pures; wp_apply twp_poly_deg; wp_pures.
rewrite (_ : (Poly.deg x p + 1)%Z = Z.of_nat (Poly.deg x p + 1)); last lia.
by wp_apply (twp_poly_cont_loop x p 0).
Qed.

Lemma twp_poly_prs x (fuel : nat) a b E Ψ :
  Ψ (repr (Poly.prs x gc dv fuel a b)) ⊢
  WP poly_prs eqv lev gcv dvv (repr x) #fuel (repr a) (repr b) @ E [{ Ψ }].
Proof.
elim: fuel a b Ψ => [|fuel IH] a b Ψ; iIntros "HΨ"; wp_rec; wp_pures.
  by iApply "HΨ".
rewrite -repr_poly_zero; wp_apply twp_poly_eq.
rewrite /=; case: bool_decide; wp_pures; first by iApply "HΨ".
wp_apply twp_poly_prem; wp_pures.
wp_apply twp_poly_cont; wp_apply twp_poly_div_lvl; wp_pures.
rewrite (_ : (S fuel - 1)%Z = fuel); last lia.
by wp_apply IH.
Qed.

Lemma twp_poly_gcd_lvl x p q E Ψ :
  Ψ (repr (Poly.gcd_lvl x gc dv p q)) ⊢
  WP poly_gcd_lvl eqv lev gcv dvv (repr x) (repr p) (repr q) @ E [{ Ψ }].
Proof.
have h2 k : (Z.of_nat k + 2)%Z = Z.of_nat (k + 2) by lia.
iIntros "HΨ"; wp_lam; wp_pures; rewrite -repr_poly_zero /Poly.gcd_lvl.
wp_apply twp_poly_eq; case: bool_decide; wp_pures; first by iApply "HΨ".
wp_apply twp_poly_eq; case: bool_decide; wp_pures; first by iApply "HΨ".
wp_apply twp_poly_cont; wp_pures; wp_apply twp_poly_cont; wp_pures.
wp_apply twp_poly_div_lvl; wp_pures; wp_apply twp_poly_div_lvl; wp_pures.
wp_apply twp_poly_deg; wp_pures; wp_apply twp_poly_deg; wp_pures.
case: (Nat.ltb_spec (Poly.deg x (Poly.div_lvl x dv p (Poly.cont x gc p)))
                   (Poly.deg x (Poly.div_lvl x dv q (Poly.cont x gc q))))
  => [lt|ge].
- rewrite bool_decide_eq_true_2; last lia.
  wp_pures; rewrite h2; wp_apply twp_poly_prs; wp_pures; wp_apply gcP.
  by wp_apply twp_poly_mul.
- rewrite bool_decide_eq_false_2; last lia.
  wp_pures; rewrite h2; wp_apply twp_poly_prs; wp_pures; wp_apply gcP.
  by wp_apply twp_poly_mul.
Qed.

End Level.

Lemma twp_int_gcd (a b : Z) E Ψ :
  Ψ #(Z.gcd a b) ⊢ WP int_gcd #a #b @ E [{ Ψ }].
Proof.
move e: (Z.to_nat (Z.abs b)) => n.
elim/lt_wf_ind: n a b Ψ e => n IH a b Ψ e; iIntros "HΨ"; wp_rec; wp_pures.
case: (decide (b = 0%Z)) => [->|nb].
  rewrite bool_decide_eq_true_2 // Z.gcd_0_r; wp_pures.
  case_bool_decide; wp_pures.
    by rewrite Z.abs_neq; last lia.
  by rewrite Z.abs_eq; last lia.
rewrite bool_decide_eq_false_2; last by case.
wp_pures; have lt := Z.rem_bound_abs a b nb.
wp_apply (IH (Z.to_nat (Z.abs (Z.rem a b)))); [lia|done|].
rewrite (_ : Z.gcd b (Z.rem a b) = Z.gcd a b) //.
by rewrite Z.gcd_comm Z.gcd_rem // Z.gcd_comm.
Qed.

Lemma twp_poly_div_vs (vs : list T) p q E Ψ :
  Ψ (repr ((Poly.ops vs).2 p q)) ⊢
  WP poly_div_vs eqv lev (repr vs) (repr p) (repr q) @ E [{ Ψ }].
Proof.
have eN : NILV = repr (∅ : MSet.mset T).
  by rewrite /repr_mset /= [@repr_list]unlock.
elim: vs p q E Ψ => [|x vs IH] p q E Ψ; iIntros "HΨ".
  rewrite repr_listE /=; wp_rec; wp_pures; rewrite eN.
  wp_apply twp_poly_coeff; wp_apply twp_poly_coeff; wp_pures.
  by wp_apply twp_poly_const.
rewrite [repr (x :: vs)]repr_listE /=; wp_rec; wp_pures.
wp_apply (twp_poly_div_lvl (Poly.ops vs).2); last done.
move=> a b E' Φ; iIntros "HΦ"; wp_pures.
by iApply IH.
Qed.

Lemma twp_poly_gcd_vs (vs : list T) p q E Ψ :
  Ψ (repr ((Poly.ops vs).1 p q)) ⊢
  WP poly_gcd_vs eqv lev (repr vs) (repr p) (repr q) @ E [{ Ψ }].
Proof.
have eN : NILV = repr (∅ : MSet.mset T).
  by rewrite /repr_mset /= [@repr_list]unlock.
elim: vs p q E Ψ => [|x vs IH] p q E Ψ; iIntros "HΨ".
  rewrite repr_listE /=; wp_rec; wp_pures; rewrite eN.
  wp_apply twp_poly_coeff; wp_apply twp_poly_coeff; wp_apply twp_int_gcd.
  by wp_apply twp_poly_const.
rewrite [repr (x :: vs)]repr_listE /=; wp_rec; wp_pures.
wp_apply (twp_poly_gcd_lvl (Poly.ops vs).1 (Poly.ops vs).2); last done.
  move=> a b E' Φ; iIntros "HΦ"; wp_pures.
  by iApply IH.
move=> a b E' Φ; iIntros "HΦ"; wp_pures.
by iApply twp_poly_div_vs.
Qed.

Lemma twp_poly_gcd p q E Ψ :
  Ψ (repr (Poly.gcd p q)) ⊢
  WP poly_gcd eqv lev (repr p) (repr q) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam; wp_pures.
wp_apply twp_poly_vars; wp_apply twp_poly_vars; wp_apply twp_append_lists.
wp_apply (twp_remove_dups_list eqv) => //.
  by iIntros "%a %b %Φ _ HΦ"; wp_apply eqvP; iApply "HΦ".
iIntros "_"; wp_pures.
by wp_apply twp_poly_gcd_vs.
Qed.

Lemma twp_poly_div p q E Ψ :
  Ψ (repr (Poly.div p q)) ⊢
  WP poly_div eqv lev (repr p) (repr q) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam; wp_pures.
wp_apply twp_poly_vars; wp_apply twp_poly_vars; wp_apply twp_append_lists.
wp_apply (twp_remove_dups_list eqv) => //.
  by iIntros "%a %b %Φ _ HΦ"; wp_apply eqvP; iApply "HΦ".
iIntros "_"; wp_pures.
by wp_apply twp_poly_div_vs.
Qed.

Lemma twp_poly_first_neg p E Ψ :
  Ψ #(Poly.first_neg p) ⊢ WP poly_first_neg eqv lev (repr p) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam; wp_pures; wp_apply (twp_mset_disj_union _ mleP).
rewrite /Poly.first_neg /repr_mset.
case: (elements (SMS.pos (Poly.car p) ⊎ SMS.neg (Poly.car p))) => [|m ms];
  rewrite repr_listE /=; wp_pures; first by iApply "HΨ".
by wp_apply twp_poly_coeff; wp_pures.
Qed.

Lemma twp_poly_cancel_with g p q p' q' E Ψ :
  Ψ (repr (Poly.cancel_with g p q p' q')) ⊢
  WP poly_cancel_with eqv lev (repr g) (repr p) (repr q) (repr p') (repr q')
    @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam; wp_pures; rewrite /Poly.cancel_with bool_decide_and.
wp_apply twp_poly_mul; wp_apply twp_poly_eq.
case: bool_decide; wp_pures; last by iApply "HΨ".
wp_apply twp_poly_mul; wp_apply twp_poly_eq.
case: bool_decide; wp_pures; last by iApply "HΨ".
wp_apply twp_poly_first_neg.
case: Poly.first_neg; wp_pures; last by iApply "HΨ".
wp_apply twp_poly_opp; wp_apply twp_poly_opp; wp_pures.
by iApply "HΨ".
Qed.

Lemma twp_poly_cancel p q E Ψ :
  Ψ (repr (Poly.cancel p q)) ⊢
  WP poly_cancel eqv lev (repr p) (repr q) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam; wp_pures; wp_apply twp_poly_gcd; wp_pures.
wp_apply twp_poly_div; wp_apply twp_poly_div.
by wp_apply twp_poly_cancel_with.
Qed.

End Proofs.
