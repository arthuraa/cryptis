(* HeapLang implementations of the signed-multiset operations of
   [cryptis.lib.sms], parameterised by HeapLang closures for the element
   operations, as in [primitives/mset.v]: an equality test [eq] and, where
   sorting is needed, a test [le] for [MSet.le].  [sms_to] takes two
   multisets and returns their differences, which cancels their common
   elements; [sms_disj_union], [sms_bind] and [sms_map] end with it.  The specs
   are continuation-style, like the [twp_hl_*] specs in [pre_term.v].  A signed
   multiset is represented by the pair of its sides ([repr_sms]). *)

From mathcomp Require Import ssreflect.
From stdpp Require Import list.
From iris.heap_lang Require Import notation proofmode.
From cryptis.lib Require Import repr list mset sms.
From cryptis.primitives Require Import mset.

Unset Printing Implicit Defensive.

#[global] Instance repr_prod {A B} `{!Repr A, !Repr B} : Repr (A * B) :=
  λ p, (repr p.1, repr p.2)%V.

#[global] Instance repr_sms {T} `{!Repr T, EqDecision T, Lexico T}
  `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)} :
  Repr (SMS.sms T) := λ s, repr (SMS.pos s, SMS.neg s).

Lemma repr_smsE {T} `{!Repr T, EqDecision T, Lexico T}
    `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)} (s : SMS.sms T) :
  repr s = repr (SMS.pos s, SMS.neg s).
Proof. done. Qed.

(** ** Implementation *)

Definition sms_to : val := λ: "eq" "X" "Y",
  (mset_difference "eq" "X" "Y", mset_difference "eq" "Y" "X").

Definition sms_eq : val := λ: "eq" "s1" "s2",
  mset_eq "eq" (Fst "s1") (Fst "s2") && mset_eq "eq" (Snd "s1") (Snd "s2").

Definition sms_inv : val := λ: "s", (Snd "s", Fst "s").

Definition sms_disj_union : val := λ: "eq" "le" "s1" "s2",
  sms_to "eq" (mset_disj_union "le" (Fst "s1") (Fst "s2"))
    (mset_disj_union "le" (Snd "s1") (Snd "s2")).

Definition sms_count : val := λ: "eq" "x" "s",
  mset_count "eq" "x" (Fst "s") - mset_count "eq" "x" (Snd "s").

(* Calls [f] once per element, collecting both sides of the results. *)
Definition sms_flat : val := λ: "f" "l",
  foldr_list
    (λ: "x" "acc",
       let: "s" := "f" "x" in
       (append_lists (Fst "s") (Fst "acc"),
        append_lists (Snd "s") (Snd "acc")))
    ([], []) "l".

Definition sms_bind : val := λ: "eq" "le" "f" "s",
  let: "P" := sms_flat "f" (Fst "s") in
  let: "N" := sms_flat "f" (Snd "s") in
  sms_to "eq" (mset_of_list "le" (append_lists (Fst "P") (Snd "N")))
    (mset_of_list "le" (append_lists (Snd "P") (Fst "N"))).

(* [f] need not be monotone or injective, so the images are sorted and
   cancelled again. *)
Definition sms_map : val := λ: "eq" "le" "f" "s",
  sms_to "eq" (mset_of_list "le" (map_list "f" (Fst "s")))
    (mset_of_list "le" (map_list "f" (Snd "s"))).

Section Proofs.

Context `{!heapGS Σ}.
Context {T : Type} `{!Repr T, EqDecision T, Lexico T}
  `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)}.
Context (eqv lev : val).
Hypothesis eqvP : ∀ (x y : T) E Ψ,
  Ψ #(bool_decide (x = y)) ⊢ WP eqv (repr x) (repr y) @ E [{ Ψ }].
Hypothesis levP : ∀ (x y : T) E Ψ,
  Ψ #(bool_decide (MSet.le x y)) ⊢ WP lev (repr x) (repr y) @ E [{ Ψ }].

Implicit Types (x : T) (s : SMS.sms T).

Lemma twp_sms_to (X Y : MSet.mset T) E Ψ :
  Ψ (repr (SMS.to X Y)) ⊢ WP sms_to eqv (repr X) (repr Y) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam; wp_pures.
wp_apply (twp_mset_difference eqv eqvP).
wp_apply (twp_mset_difference eqv eqvP).
wp_pures; by iApply "HΨ".
Qed.

Lemma twp_sms_eq s1 s2 E Ψ :
  Ψ #(bool_decide (s1 = s2)) ⊢ WP sms_eq eqv (repr s1) (repr s2) @ E [{ Ψ }].
Proof.
have -> : bool_decide (s1 = s2) =
    bool_decide (SMS.pos s1 = SMS.pos s2) &&
    bool_decide (SMS.neg s1 = SMS.neg s2).
  case: (bool_decide_reflect (s1 = s2)) => [->|ne].
    by rewrite !bool_decide_eq_true_2.
  case: (bool_decide_reflect (SMS.pos s1 = SMS.pos s2)) => // ep.
  case: (bool_decide_reflect (SMS.neg s1 = SMS.neg s2)) => // en.
  by case: ne; apply: SMS.sms_eq.
rewrite [repr s1]repr_smsE [repr s2]repr_smsE /repr_prod /=.
iIntros "HΨ"; wp_lam; wp_pures.
wp_apply (twp_mset_eq eqv eqvP).
case: bool_decide; wp_pures; last by iApply "HΨ".
by wp_apply (twp_mset_eq eqv eqvP).
Qed.

Lemma twp_sms_inv s E Ψ :
  Ψ (repr (SMS.inv s)) ⊢ WP sms_inv (repr s) @ E [{ Ψ }].
Proof.
rewrite [repr s]repr_smsE /repr_prod /=; iIntros "HΨ"; wp_lam; wp_pures.
by iApply "HΨ".
Qed.

Lemma twp_sms_disj_union s1 s2 E Ψ :
  Ψ (repr (s1 ⊎ s2)) ⊢
  WP sms_disj_union eqv lev (repr s1) (repr s2) @ E [{ Ψ }].
Proof.
rewrite [repr s1]repr_smsE [repr s2]repr_smsE /repr_prod /=.
iIntros "HΨ"; wp_lam; wp_pures.
wp_apply (twp_mset_disj_union lev levP); wp_pures.
wp_apply (twp_mset_disj_union lev levP).
by wp_apply twp_sms_to.
Qed.

Lemma twp_sms_count x s E Ψ :
  Ψ #(SMS.count x s) ⊢ WP sms_count eqv (repr x) (repr s) @ E [{ Ψ }].
Proof.
rewrite [repr s]repr_smsE /repr_prod /=; iIntros "HΨ"; wp_lam; wp_pures.
wp_apply (twp_mset_count eqv eqvP); wp_pures.
wp_apply (twp_mset_count eqv eqvP); wp_pures.
by iApply "HΨ".
Qed.

End Proofs.

Section BindProofs.

Context `{!heapGS Σ}.
Context {T U : Type} `{!Repr T, !Repr U}.
Context `{EqDecision T, Lexico T}
  `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)}.
Context `{EqDecision U, Lexico U}
  `{!StrictOrder (@lexico U _), !TrichotomyT (@lexico U _)}.
Context (eqv lev : val).
Hypothesis eqvP : ∀ (x y : U) E Ψ,
  Ψ #(bool_decide (x = y)) ⊢ WP eqv (repr x) (repr y) @ E [{ Ψ }].
Hypothesis levP : ∀ (x y : U) E Ψ,
  Ψ #(bool_decide (MSet.le x y)) ⊢ WP lev (repr x) (repr y) @ E [{ Ψ }].

Implicit Types (s : SMS.sms T).

#[local] Lemma twp_sms_flat (f : T → SMS.sms U) (fv : val) (l : list T) E Ψ :
  (∀ x E Ψ, Ψ (repr (f x)) ⊢ WP fv (repr x) @ E [{ Ψ }]) →
  Ψ (repr (l ≫= λ x, elements (SMS.pos (f x))),
     repr (l ≫= λ x, elements (SMS.neg (f x))))%V ⊢
  WP sms_flat fv (repr l) @ E [{ Ψ }].
Proof.
move=> fvP; iIntros "HΨ"; wp_lam; wp_pures.
have -> : (NONEV, NONEV)%V = repr (([] : list U), ([] : list U)).
  by rewrite /= [@repr_list]unlock.
wp_apply (twp_foldr_list (λ x (acc : list U * list U),
            (elements (SMS.pos (f x)) ++ acc.1,
             elements (SMS.neg (f x)) ++ acc.2)) _ l ([], [])) => //.
  move=> x [a1 a2]; iIntros "%Φ _ HΦ"; rewrite /repr_prod /=; wp_pures.
  wp_apply fvP; rewrite /repr_sms /repr_prod /=; wp_pures.
  wp_apply twp_append_lists; wp_pures; wp_apply twp_append_lists; wp_pures.
  by iApply "HΦ".
iIntros "_"; have -> : ∀ l', foldr (λ x (acc : list U * list U),
    (elements (SMS.pos (f x)) ++ acc.1,
     elements (SMS.neg (f x)) ++ acc.2)) ([], []) l' =
  (l' ≫= λ x, elements (SMS.pos (f x)), l' ≫= λ x, elements (SMS.neg (f x))).
  by elim => //= x l' ->.
by iApply "HΨ".
Qed.

Lemma twp_sms_bind (f : T → SMS.sms U) (fv : val) s E Ψ :
  (∀ x E Ψ, Ψ (repr (f x)) ⊢ WP fv (repr x) @ E [{ Ψ }]) →
  Ψ (repr (SMS.bind f s)) ⊢ WP sms_bind eqv lev fv (repr s) @ E [{ Ψ }].
Proof.
move=> fvP; rewrite /SMS.bind /MSet.bind -!MSet.of_list_app.
rewrite [repr s]repr_smsE /repr_prod /=; iIntros "HΨ"; wp_lam; wp_pures.
wp_apply (twp_sms_flat f fv _ _ _ fvP); wp_pures.
wp_apply (twp_sms_flat f fv _ _ _ fvP); wp_pures.
wp_apply twp_append_lists; wp_apply (twp_mset_of_list lev levP); wp_pures.
wp_apply twp_append_lists; wp_apply (twp_mset_of_list lev levP).
by wp_apply (twp_sms_to eqv eqvP).
Qed.

Lemma twp_sms_map (f : T → U) (fv : val) s E Ψ :
  (∀ x E Ψ, Ψ (repr (f x)) ⊢ WP fv (repr x) @ E [{ Ψ }]) →
  Ψ (repr (SMS.map f s)) ⊢ WP sms_map eqv lev fv (repr s) @ E [{ Ψ }].
Proof.
move=> fvP; rewrite SMS.map_pos_neg /MSet.map.
have fvT l :
    Forall (λ x, [[{ True }]] fv (repr x) @ E [[{ RET repr (f x); True }]]) l.
  by apply/Forall_forall => x _ Φ; iIntros "_ HΦ"; wp_apply fvP; iApply "HΦ".
have em l : List.map f l = f <$> l by elim: l => //= x l ->.
rewrite [repr s]repr_smsE /repr_prod /=; iIntros "HΨ"; wp_lam; wp_pures.
wp_apply (twp_map_list f _ _ _ (fvT _)) => //; iIntros "_"; rewrite em.
wp_apply (twp_mset_of_list lev levP); wp_pures.
wp_apply (twp_map_list f _ _ _ (fvT _)) => //; iIntros "_"; rewrite em.
wp_apply (twp_mset_of_list lev levP).
by wp_apply (twp_sms_to eqv eqvP).
Qed.

End BindProofs.
