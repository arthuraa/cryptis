(* HeapLang implementations of the finite-map operations of [cryptis.lib.fmap],
   parameterised as in [primitives/mset.v] by HeapLang closures on keys, an
   equality test [eq] and a test [le] for [MSet.le], and by an equality test
   [eqs] on values, which drops the bindings to the default.  The default is
   passed as a value.  A finite map is represented by its sorted list of
   bindings ([repr_fmap]), whose pairs use [repr_prod] from [primitives/sms.v].
   [fmap_merge] merges the two lists in one pass, and [fmap_insert] and
   [fmap_delete] are merges, as in [FMap].  [fmap_eq] and [fmap_le] compare
   finite maps themselves, given a test [les] for [MSet.le] on values, so that
   finite maps can be keys of other finite maps.  The specs are
   continuation-style, like those of [primitives/mset.v]. *)

From mathcomp Require Import ssreflect.
From stdpp Require Import list.
From iris.heap_lang Require Import notation proofmode.
From cryptis.lib Require Import repr list mset fmap.
From cryptis.primitives Require Import sms.

Unset Printing Implicit Defensive.

#[global] Instance repr_fmap {T S} `{!Repr T, !Repr S, Lexico T}
  `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)} `{EqDecision S}
  {d : S} : Repr (FMap.fmap T S d) := λ m, repr (FMap.to_list m).

Lemma repr_fmapE {T S} `{!Repr T, !Repr S, Lexico T}
    `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)} `{EqDecision S}
    {d : S} (m : FMap.fmap T S d) :
  repr m = repr (FMap.to_list m).
Proof. done. Qed.

(** ** Implementations *)

Definition fmap_empty : val := NONEV.

Definition fmap_lookup : val := rec: "loop" "eq" "d" "k" "m" :=
  match: "m" with
    NONE => "d"
  | SOME "p" =>
    if: "eq" "k" (Fst (Fst "p")) then Snd (Fst "p")
    else "loop" "eq" "d" "k" (Snd "p")
  end.

Definition fmap_cons_nd : val := λ: "eq" "d" "k" "v" "l",
  if: "eq" "v" "d" then "l" else SOME (("k", "v"), "l").

Definition fmap_singleton : val := λ: "eq" "d" "k" "v",
  fmap_cons_nd "eq" "d" "k" "v" NONEV.

Definition fmap_eq : val := λ: "eq" "eqs" "m1" "m2",
  eq_list
    (λ: "p1" "p2", "eq" (Fst "p1") (Fst "p2") && "eqs" (Snd "p1") (Snd "p2"))
    "m1" "m2".

Definition fmap_le : val := λ: "eq" "le" "eqs" "les" "m1" "m2",
  leq_list
    (λ: "p1" "p2", "eq" (Fst "p1") (Fst "p2") && "eqs" (Snd "p1") (Snd "p2"))
    (λ: "p1" "p2",
       if: "eq" (Fst "p1") (Fst "p2") then "les" (Snd "p1") (Snd "p2")
       else "le" (Fst "p1") (Fst "p2"))
    "m1" "m2".

Definition fmap_merge_loop : val :=
  rec: "loop" "eq" "le" "cons" "f" "d1" "d2" "xs" "ys" :=
  match: "xs" with
    NONE =>
    match: "ys" with
      NONE => NONE
    | SOME "q" =>
      "cons" (Fst (Fst "q")) ("f" "d1" (Snd (Fst "q")))
        ("loop" "eq" "le" "cons" "f" "d1" "d2" NONE (Snd "q"))
    end
  | SOME "p" =>
    match: "ys" with
      NONE =>
      "cons" (Fst (Fst "p")) ("f" (Snd (Fst "p")) "d2")
        ("loop" "eq" "le" "cons" "f" "d1" "d2" (Snd "p") NONE)
    | SOME "q" =>
      let: "k1" := Fst (Fst "p") in
      let: "k2" := Fst (Fst "q") in
      if: "eq" "k1" "k2" then
        "cons" "k1" ("f" (Snd (Fst "p")) (Snd (Fst "q")))
          ("loop" "eq" "le" "cons" "f" "d1" "d2" (Snd "p") (Snd "q"))
      else if: "le" "k1" "k2" then
        "cons" "k1" ("f" (Snd (Fst "p")) "d2")
          ("loop" "eq" "le" "cons" "f" "d1" "d2" (Snd "p") "ys")
      else
        "cons" "k2" ("f" "d1" (Snd (Fst "q")))
          ("loop" "eq" "le" "cons" "f" "d1" "d2" "xs" (Snd "q"))
    end
  end.

Definition fmap_merge : val := λ: "eq" "le" "eqs" "f" "d1" "d2" "m1" "m2",
  let: "d" := "f" "d1" "d2" in
  let: "cons" := λ: "k" "v" "l", fmap_cons_nd "eqs" "d" "k" "v" "l" in
  fmap_merge_loop "eq" "le" "cons" "f" "d1" "d2" "m1" "m2".

Definition fmap_insert : val := λ: "eq" "le" "eqs" "d" "k" "v" "m",
  fmap_merge "eq" "le" "eqs"
    (λ: "a" "o", match: "o" with NONE => "a" | SOME "b" => "b" end)
    "d" NONEV "m" (SOME (("k", SOME "v"), NONEV)).

Definition fmap_delete : val := λ: "eq" "le" "eqs" "d" "k" "m",
  fmap_insert "eq" "le" "eqs" "d" "k" "d" "m".

Definition fmap_map_loop : val := rec: "loop" "cons" "f" "m" :=
  match: "m" with
    NONE => NONE
  | SOME "p" =>
    "cons" (Fst (Fst "p")) ("f" (Snd (Fst "p"))) ("loop" "cons" "f" (Snd "p"))
  end.

Definition fmap_map : val := λ: "eqs" "f" "d" "m",
  let: "d'" := "f" "d" in
  let: "cons" := λ: "k" "v" "l", fmap_cons_nd "eqs" "d'" "k" "v" "l" in
  fmap_map_loop "cons" "f" "m".

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

Section Values.

Context {S : Type} `{!Repr S, EqDecision S} (d : S) (eqsv : val).
Hypothesis eqsvP : ∀ (x y : S) E Ψ,
  Ψ #(bool_decide (x = y)) ⊢ WP eqsv (repr x) (repr y) @ E [{ Ψ }].

Implicit Types (k : T) (v : S) (l : list (T * S)) (m : FMap.fmap T S d).

Lemma repr_fmap_empty : repr (∅ : FMap.fmap T S d) = fmap_empty.
Proof. by rewrite repr_fmapE FMap.to_listE /= [@repr_list]unlock. Qed.

Lemma twp_fmap_empty E Ψ :
  Ψ (repr (∅ : FMap.fmap T S d)) ⊢ WP Val fmap_empty @ E [{ Ψ }].
Proof. by rewrite repr_fmap_empty; iIntros "HΨ"; wp_pures. Qed.

Lemma twp_fmap_lookup k m E Ψ :
  Ψ (repr (m !!! k)) ⊢
  WP fmap_lookup eqv (repr d) (repr k) (repr m) @ E [{ Ψ }].
Proof.
have -> : m !!! k = FMap.lookup_list d k (FMap.to_list m).
  by rewrite FMap.lookupE FMap.to_listE.
rewrite repr_fmapE [@repr_list]unlock.
elim: (FMap.to_list m) Ψ => [|[k' v] l IH] Ψ /=; iIntros "HΨ"; wp_rec; wp_pures.
  by iApply "HΨ".
wp_apply eqvP; case: bool_decide; wp_pures; first by iApply "HΨ".
by iApply IH.
Qed.

Lemma twp_fmap_cons_nd k v l E Ψ :
  Ψ (repr (FMap.cons_nd d k v l)) ⊢
  WP fmap_cons_nd eqsv (repr d) (repr k) (repr v) (repr l) @ E [{ Ψ }].
Proof.
rewrite /FMap.cons_nd; iIntros "HΨ"; wp_lam; wp_pures; wp_apply eqsvP.
case: bool_decide; wp_pures; first by iApply "HΨ".
by rewrite (repr_listE ((k, v) :: l)).
Qed.

Lemma twp_fmap_singleton k v E Ψ :
  Ψ (repr ({[k := v]} : FMap.fmap T S d)) ⊢
  WP fmap_singleton eqsv (repr d) (repr k) (repr v) @ E [{ Ψ }].
Proof.
have e : NONEV = repr ([] : list (T * S)) by rewrite repr_listE.
rewrite repr_fmapE FMap.to_listE FMap.car_singleton.
iIntros "HΨ"; wp_lam; wp_pures; rewrite e.
by wp_apply twp_fmap_cons_nd.
Qed.

Lemma twp_fmap_eq m1 m2 E Ψ :
  Ψ #(bool_decide (m1 = m2)) ⊢
  WP fmap_eq eqv eqsv (repr m1) (repr m2) @ E [{ Ψ }].
Proof.
have -> : bool_decide (m1 = m2) =
    bool_decide (FMap.to_list m1 = FMap.to_list m2).
  by apply: bool_decide_ext; rewrite !FMap.to_listE;
    split=> [->|/FMap.car_inj].
rewrite !repr_fmapE; iIntros "HΨ"; wp_lam; wp_pures.
iApply (twp_eq_list with "HΨ") => -[k1 v1] [k2 v2] Φ _.
iIntros "HΦ"; wp_pures; wp_apply eqvP.
case: (bool_decide_reflect (k1 = k2)) => [<-|nk]; wp_pures; last first.
  by rewrite bool_decide_false //; case.
wp_apply eqsvP; rewrite (bool_decide_ext _ (v1 = v2)) //.
by split=> [[]|->].
Qed.

End Values.

Section Merge.

Context {S1 S2 S3 : Type} `{!Repr S1, !Repr S2, !Repr S3}.
Context `{EqDecision S1, EqDecision S2, EqDecision S3}.
Context (d1 : S1) (d2 : S2) (eqsv : val).
Hypothesis eqsvP : ∀ (x y : S3) E Ψ,
  Ψ #(bool_decide (x = y)) ⊢ WP eqsv (repr x) (repr y) @ E [{ Ψ }].

#[local] Lemma merge_list_cons (f : S1 → S2 → S3) k1 a xs k2 b ys :
  FMap.merge_list d1 d2 f ((k1, a) :: xs) ((k2, b) :: ys) =
  if bool_decide (k1 = k2) then
    FMap.cons_nd (f d1 d2) k1 (f a b) (FMap.merge_list d1 d2 f xs ys)
  else if bool_decide (MSet.le k1 k2) then
    FMap.cons_nd (f d1 d2) k1 (f a d2)
      (FMap.merge_list d1 d2 f xs ((k2, b) :: ys))
  else
    FMap.cons_nd (f d1 d2) k2 (f d1 b)
      (FMap.merge_list d1 d2 f ((k1, a) :: xs) ys).
Proof.
rewrite /=; case: (trichotomyT lexico k1 k2) => [[k12|<-]|k21].
- have ne : k1 ≠ k2 by exact: FMap.lexico_neq k12.
  rewrite (bool_decide_false _ ne).
  by rewrite (bool_decide_true (MSet.le k1 k2) (or_intror k12)).
- by rewrite (bool_decide_true (k1 = k1) eq_refl).
- have ne : k1 ≠ k2 by move=> e; apply: FMap.lexico_neq k21 (eq_sym e).
  have nle : ¬ MSet.le k1 k2.
    case=> [//|k12]; exact: (irreflexivity lexico k1 (transitivity k12 k21)).
  by rewrite (bool_decide_false _ ne) (bool_decide_false _ nle).
Qed.

#[local] Lemma twp_fmap_merge_loop (f : S1 → S2 → S3) (fv consv : val)
    xs ys E Ψ :
  (∀ a b E Ψ, Ψ (repr (f a b)) ⊢ WP fv (repr a) (repr b) @ E [{ Ψ }]) →
  (∀ k v (l : list (T * S3)) E Ψ,
      Ψ (repr (FMap.cons_nd (f d1 d2) k v l)) ⊢
      WP consv (repr k) (repr v) (repr l) @ E [{ Ψ }]) →
  Ψ (repr (FMap.merge_list d1 d2 f xs ys)) ⊢
  WP fmap_merge_loop eqv lev consv fv (repr d1) (repr d2) (repr xs) (repr ys)
    @ E [{ Ψ }].
Proof.
move=> fvP consP; rewrite [@repr_list]unlock /repr_prod in consP *.
elim: xs ys E Ψ => [|[k1 a] xs IH1] ys E Ψ.
  elim: ys E Ψ => [|[k2 b] ys IH2] E Ψ /=; iIntros "HΨ"; wp_rec; wp_pures.
    by iApply "HΨ".
  wp_apply IH2; wp_pures; wp_apply fvP; wp_pures; by wp_apply consP.
elim: ys E Ψ => [|[k2 b] ys IH2] E Ψ.
  rewrite /=; iIntros "HΨ"; wp_rec; wp_pures.
  wp_apply (IH1 []); wp_pures; wp_apply fvP; wp_pures; by wp_apply consP.
rewrite merge_list_cons [repr ((k1, a) :: _)]/= [repr ((k2, b) :: _)]/=.
iIntros "HΨ"; wp_rec; wp_pures.
wp_apply eqvP; case: (bool_decide_reflect (k1 = k2)) => [<-|ne]; wp_pures.
  wp_apply (IH1 ys); wp_pures; wp_apply fvP; wp_pures; by wp_apply consP.
wp_apply levP; case: (bool_decide_reflect (MSet.le k1 k2)) => [le|nle].
  wp_pures; wp_apply (IH1 ((k2, b) :: ys)); wp_pures; wp_apply fvP; wp_pures.
  by wp_apply consP.
wp_pures; wp_apply IH2; wp_pures; wp_apply fvP; wp_pures; by wp_apply consP.
Qed.

Lemma twp_fmap_merge (f : S1 → S2 → S3) (fv : val)
    (m1 : FMap.fmap T S1 d1) (m2 : FMap.fmap T S2 d2) E Ψ :
  (∀ a b E Ψ, Ψ (repr (f a b)) ⊢ WP fv (repr a) (repr b) @ E [{ Ψ }]) →
  Ψ (repr (FMap.merge f m1 m2)) ⊢
  WP fmap_merge eqv lev eqsv fv (repr d1) (repr d2) (repr m1) (repr m2)
    @ E [{ Ψ }].
Proof.
move=> fvP; rewrite !repr_fmapE !FMap.to_listE [FMap.merge]unlock /=.
iIntros "HΨ"; wp_lam; wp_pures.
wp_apply fvP; wp_pures.
wp_apply (twp_fmap_merge_loop f fv); first exact: fvP.
  move=> k v l E' Φ; iIntros "HΦ"; wp_pures.
  by wp_apply (twp_fmap_cons_nd (f d1 d2) eqsv eqsvP).
by [].
Qed.

End Merge.

Section Insert.

Context {S : Type} `{!Repr S, EqDecision S} (d : S) (eqsv : val).
Hypothesis eqsvP : ∀ (x y : S) E Ψ,
  Ψ #(bool_decide (x = y)) ⊢ WP eqsv (repr x) (repr y) @ E [{ Ψ }].

Implicit Types (k : T) (v : S) (m : FMap.fmap T S d).

Lemma twp_fmap_insert k v m E Ψ :
  Ψ (repr (<[k:=v]> m)) ⊢
  WP fmap_insert eqv lev eqsv (repr d) (repr k) (repr v) (repr m) @ E [{ Ψ }].
Proof.
have e : (SOMEV ((repr k, SOMEV (repr v)), NONEV))%V =
    repr ({[k := Some v]} : FMap.fmap T (option S) None).
  rewrite repr_fmapE FMap.to_listE FMap.car_singleton /FMap.cons_nd.
  rewrite bool_decide_false //.
  by rewrite [@repr_list]unlock.
iIntros "HΨ"; wp_lam; wp_pures; rewrite e.
wp_apply (twp_fmap_merge d None eqsv eqsvP (λ a o, default a o)).
  by move=> a [b|] E' Φ; iIntros "HΦ"; wp_pures.
by [].
Qed.

Lemma twp_fmap_delete k m E Ψ :
  Ψ (repr (delete k m)) ⊢
  WP fmap_delete eqv lev eqsv (repr d) (repr k) (repr m) @ E [{ Ψ }].
Proof. iIntros "HΨ"; wp_lam; wp_pures; by wp_apply twp_fmap_insert. Qed.

End Insert.

Section Map.

Context {S1 S2 : Type} `{!Repr S1, !Repr S2, EqDecision S1, EqDecision S2}.
Context (d1 : S1) (eqsv : val).
Hypothesis eqsvP : ∀ (x y : S2) E Ψ,
  Ψ #(bool_decide (x = y)) ⊢ WP eqsv (repr x) (repr y) @ E [{ Ψ }].

#[local] Lemma twp_fmap_map_loop (f : S1 → S2) (fv consv : val) xs E Ψ :
  (∀ a E Ψ, Ψ (repr (f a)) ⊢ WP fv (repr a) @ E [{ Ψ }]) →
  (∀ k v (l : list (T * S2)) E Ψ,
      Ψ (repr (FMap.cons_nd (f d1) k v l)) ⊢
      WP consv (repr k) (repr v) (repr l) @ E [{ Ψ }]) →
  Ψ (repr (FMap.merge_list d1 tt (λ a _, f a) xs [])) ⊢
  WP fmap_map_loop consv fv (repr xs) @ E [{ Ψ }].
Proof.
move=> fvP consP; rewrite [@repr_list]unlock /repr_prod in consP *.
elim: xs E Ψ => [|[k a] xs IH] E Ψ /=; iIntros "HΨ"; wp_rec; wp_pures.
  by iApply "HΨ".
wp_apply IH; wp_pures; wp_apply fvP; wp_pures; by wp_apply consP.
Qed.

Lemma twp_fmap_map (f : S1 → S2) (fv : val) (m : FMap.fmap T S1 d1) E Ψ :
  (∀ a E Ψ, Ψ (repr (f a)) ⊢ WP fv (repr a) @ E [{ Ψ }]) →
  Ψ (repr (FMap.map f m)) ⊢ WP fmap_map eqsv fv (repr d1) (repr m) @ E [{ Ψ }].
Proof.
move=> fvP; rewrite !repr_fmapE !FMap.to_listE [FMap.map]unlock.
rewrite [FMap.merge]unlock /=; iIntros "HΨ"; wp_lam; wp_pures.
wp_apply fvP; wp_pures.
wp_apply (twp_fmap_map_loop f fv); first exact: fvP.
  move=> k v l E' Φ; iIntros "HΦ"; wp_pures.
  by wp_apply (twp_fmap_cons_nd (f d1) eqsv eqsvP).
by [].
Qed.

End Map.

Section Lexico.

Context {S : Type} `{!Repr S, EqDecision S, Lexico S}
  `{!StrictOrder (@lexico S _), !TrichotomyT (@lexico S _)}.
Context (d : S) (eqsv lesv : val).
Hypothesis eqsvP : ∀ (x y : S) E Ψ,
  Ψ #(bool_decide (x = y)) ⊢ WP eqsv (repr x) (repr y) @ E [{ Ψ }].
Hypothesis lesvP : ∀ (x y : S) E Ψ,
  Ψ #(bool_decide (MSet.le x y)) ⊢ WP lesv (repr x) (repr y) @ E [{ Ψ }].

Lemma twp_fmap_le (m1 m2 : FMap.fmap T S d) E Ψ :
  Ψ #(bool_decide (MSet.le m1 m2)) ⊢
  WP fmap_le eqv lev eqsv lesv (repr m1) (repr m2) @ E [{ Ψ }].
Proof.
have -> : bool_decide (MSet.le m1 m2) =
    bool_decide (FMap.to_list m1 = FMap.to_list m2 ∨
                 lexico (FMap.to_list m1) (FMap.to_list m2)).
  apply: bool_decide_ext; rewrite /MSet.le.
  split=> -[e|l]; [left; rewrite e|right|left|right] => //.
  by apply: FMap.car_inj; rewrite -!FMap.to_listE.
rewrite !repr_fmapE; iIntros "HΨ"; wp_lam; wp_pures.
wp_apply (twp_leq_list _ _ (FMap.to_list m1) (FMap.to_list m2)).
- move=> [k1 v1] [k2 v2] Φ; iIntros "_ HΦ"; wp_pures; wp_apply eqvP.
  case: (bool_decide_reflect (k1 = k2)) => [<-|ne]; wp_pures.
    wp_apply eqsvP.
    have -> : bool_decide (v1 = v2) = bool_decide ((k1, v1) = (k1, v2)).
      by apply: bool_decide_ext; split=> [->|[]].
    by iApply "HΦ".
  have nkv : (k1, v1) ≠ (k2, v2) by move=> [/ne].
  by rewrite (bool_decide_false _ nkv); iApply "HΦ".
- move=> [k1 v1] [k2 v2] _ Φ; iIntros "_ HΦ"; wp_pures; wp_apply eqvP.
  case: (bool_decide_reflect (k1 = k2)) => [<-|ne]; wp_pures.
    wp_apply lesvP.
    have -> : bool_decide (MSet.le v1 v2) =
        bool_decide ((k1, v1) = (k1, v2) ∨ lexico (k1, v1) (k1, v2)).
      apply: bool_decide_ext; rewrite /MSet.le; split.
      + by case=> [->|l]; [left|right; right].
      + case=> [[->]|[kk|[_ l]]]; [by left| |by right].
        by case: (irreflexivity lexico k1 kk).
    by iApply "HΦ".
  wp_apply levP.
  have -> : bool_decide (MSet.le k1 k2) =
      bool_decide ((k1, v1) = (k2, v2) ∨ lexico (k1, v1) (k2, v2)).
    apply: bool_decide_ext; rewrite /MSet.le; split.
    + by case=> [/ne|l]; [|right; left].
    + by case=> [[/ne]|[l|[/ne]]]; [|right|].
  by iApply "HΦ".
- done.
- by iIntros "_".
Qed.

End Lexico.

End Proofs.
