(* HeapLang implementations of the pre-term operations behind
   [primitives/comp.v], with specs saying that each program computes the
   corresponding function of [core/pre_term].

   [cmp_term] compares two pre-terms as [PreTerm.pt_cmp] does, by constructor
   and then lexicographically ([cmp_list], [cmp_poly], [cmp_frac]);
   [eq_term] and [leq_term] are its equality and order tests.  Exponents are
   computed through their fractions ([hl_frac_of], [hl_mod_of_frac]) with the
   operations of [primitives/frac.v], and group elements through their
   Diffie-Hellman maps ([hl_dh_map], [hl_dh_of]) with those of
   [primitives/fmap.v]. *)

From mathcomp Require Import ssreflect.
From stdpp Require Import list sorting.
From iris.heap_lang Require Import notation proofmode.
From cryptis.lib Require Import repr list list_sort fmap mset sms.
From cryptis.lib Require Import poly poly_gcd frac.
From cryptis.core Require Import pre_term.
From cryptis.primitives Require Import mset sms fmap poly frac.

Unset Printing Implicit Defensive.

(** ** Comparison *)

Definition cmp_Z (c : comparison) : Z :=
  match c with Lt => -1 | Eq => 0 | Gt => 1 end.

(* Three-way comparison of two integers or of two locations. *)
Definition cmp_lit : val := λ: "x" "y",
  if: "x" = "y" then #0 else if: "x" < "y" then #(-1) else #1.

Definition cmp_op0 : val := λ: "x" "y",
  if: Fst "x" = Fst "y" then cmp_lit (Snd "x") (Snd "y")
  else cmp_lit (Fst "x") (Fst "y").

Definition cmp_op1 : val := λ: "x" "y",
  if: Fst "x" = Fst "y" then
    if: Fst "x" = #TKey_tag then cmp_lit (Snd "x") (Snd "y") else #0
  else cmp_lit (Fst "x") (Fst "y").

Definition cmp_op2 : val := λ: "x" "y", cmp_lit "x" "y".

Definition cmp_list : val := rec: "go" "c" "xs" "ys" :=
  match: "xs" with
    NONE => match: "ys" with NONE => #0 | SOME <> => #(-1) end
  | SOME "p" =>
    match: "ys" with
      NONE => #1
    | SOME "q" =>
      let: "r" := "c" (Fst "p") (Fst "q") in
      if: "r" = #0 then "go" "c" (Snd "p") (Snd "q") else "r"
    end
  end.

Definition cmp_poly : val := λ: "c" "p" "q",
  let: "cm" := (λ: "m" "n", cmp_list "c" "m" "n") in
  let: "r" := cmp_list "cm" (Fst "p") (Fst "q") in
  if: "r" = #0 then cmp_list "cm" (Snd "p") (Snd "q") else "r".

Definition cmp_frac : val := λ: "c" "f" "g",
  let: "r" := cmp_poly "c" (Fst "f") (Fst "g") in
  if: "r" = #0 then cmp_poly "c" (Snd "f") (Snd "g") else "r".

Definition cmp_entry : val := λ: "c" "e1" "e2",
  let: "r" := "c" (Fst "e1") (Fst "e2") in
  if: "r" = #0 then cmp_frac "c" (Snd "e1") (Snd "e2") else "r".

Definition cmp_term : val := rec: "cmp" "x" "y" :=
  let: "tx" := Fst "x" in
  let: "ty" := Fst "y" in
  if: "tx" = "ty" then
    let: "a" := Snd "x" in
    let: "b" := Snd "y" in
    if: "tx" = #TOp0_tag then cmp_op0 "a" "b"
    else if: "tx" = #TOp1_tag then
      let: "r" := cmp_op1 (Fst "a") (Fst "b") in
      if: "r" = #0 then "cmp" (Snd "a") (Snd "b") else "r"
    else if: "tx" = #TOp2_tag then
      let: "r" := cmp_op2 (Fst (Fst "a")) (Fst (Fst "b")) in
      if: "r" = #0 then
        let: "r" := "cmp" (Snd (Fst "a")) (Snd (Fst "b")) in
        if: "r" = #0 then "cmp" (Snd "a") (Snd "b") else "r"
      else "r"
    else if: "tx" = #TMod_tag then cmp_frac "cmp" "a" "b"
    else cmp_list (λ: "e1" "e2", cmp_entry "cmp" "e1" "e2") "a" "b"
  else cmp_lit "tx" "ty".

Definition eq_term : val := λ: "x" "y", cmp_term "x" "y" = #0.

Definition leq_term : val := λ: "x" "y", ~ (cmp_term "x" "y" = #1).

(** ** Exponents and group elements *)

Definition eq_frac : val := λ: "f" "g", frac_eq eq_term "f" "g".

Definition add_frac : val := λ: "f" "g", frac_add eq_term leq_term "f" "g".

Definition mul_frac : val := λ: "f" "g", frac_mul eq_term leq_term "f" "g".

Definition inv_frac : val := λ: "f", frac_inv eq_term leq_term "f".

Definition is_one_frac : val := λ: "f", frac_eq eq_term "f" frac_one.

Definition hl_is_mod : val := λ: "pt", Fst "pt" = #TMod_tag.

Definition hl_is_dh : val := λ: "pt", Fst "pt" = #TDH_tag.

Definition hl_frac_of : val := λ: "pt",
  if: hl_is_mod "pt" then Snd "pt" else frac_var "pt".

(* [SOME x] when the fraction is the lone atom [x]. *)
Definition hl_lone_atom : val := λ: "r",
  match: Fst (Fst "r") with
    NONE => NONE
  | SOME "c" =>
    match: Snd "c" with
      SOME <> => NONE
    | NONE =>
      match: Snd (Fst "r") with
        SOME <> => NONE
      | NONE =>
        match: Fst "c" with
          NONE => NONE
        | SOME "m" =>
          match: Snd "m" with
            SOME <> => NONE
          | NONE =>
            match: Fst (Snd "r") with
              NONE => NONE
            | SOME "e" =>
              match: Fst "e" with
                SOME <> => NONE
              | NONE =>
                match: Snd "e" with
                  SOME <> => NONE
                | NONE =>
                  match: Snd (Snd "r") with
                    SOME <> => NONE
                  | NONE => SOME (Fst "m")
                  end
                end
              end
            end
          end
        end
      end
    end
  end.

Definition hl_mod_of_frac : val := λ: "r",
  match: hl_lone_atom "r" with
    SOME "x" => "x"
  | NONE => (#TMod_tag, "r")
  end.

Definition hl_dh_map : val := λ: "pt",
  if: hl_is_dh "pt" then Snd "pt"
  else fmap_singleton eq_frac frac_zero "pt" frac_one.

Definition hl_dh_of : val := λ: "m",
  match: "m" with
    NONE => (#TDH_tag, "m")
  | SOME "p" =>
    match: Snd "p" with
      NONE =>
        if: is_one_frac (Snd (Fst "p")) then Fst (Fst "p")
        else (#TDH_tag, "m")
    | SOME <> => (#TDH_tag, "m")
    end
  end.

Definition hl_dh_add : val := λ: "m1" "m2",
  fmap_merge eq_term leq_term eq_frac add_frac frac_zero frac_zero "m1" "m2".

Definition hl_dh_opp : val := λ: "m", fmap_map eq_frac frac_opp frac_zero "m".

Definition hl_dh_scale : val := λ: "r" "m",
  fmap_map eq_frac (λ: "f", mul_frac "f" "r") frac_zero "m".

Definition hl_mul : val := λ: "t1" "t2",
  hl_mod_of_frac (mul_frac (hl_frac_of "t1") (hl_frac_of "t2")).

Definition hl_inv : val := λ: "t", hl_mod_of_frac (inv_frac (hl_frac_of "t")).

Definition hl_one : val := (#TMod_tag, frac_one).

Definition hl_sum : val := λ: "t1" "t2",
  hl_mod_of_frac (add_frac (hl_frac_of "t1") (hl_frac_of "t2")).

Definition hl_opp : val := λ: "t", hl_mod_of_frac (frac_opp (hl_frac_of "t")).

Definition hl_zero : val := (#TMod_tag, frac_zero).

Definition hl_gmul : val := λ: "t1" "t2",
  hl_dh_of (hl_dh_add (hl_dh_map "t1") (hl_dh_map "t2")).

Definition hl_ginv : val := λ: "t", hl_dh_of (hl_dh_opp (hl_dh_map "t")).

Definition hl_gone : val := (#TDH_tag, NONEV).

Definition hl_exp : val := λ: "b" "e",
  hl_dh_of (hl_dh_scale (hl_frac_of "e") (hl_dh_map "b")).

Definition texp : val := λ: "base" "exp", hl_exp "base" "exp".

(** ** Pure facts *)

Section Proofs.

Context `{!heapGS Σ}.

Implicit Types E : coPset.
Implicit Types (x y pt : PreTerm.pre_term).
Implicit Types Ψ : val → iProp Σ.

(** *** Comparison *)

Lemma twp_cmp_lit_int (n1 n2 : Z) E Ψ :
  Ψ #(cmp_Z (Z.compare n1 n2)) ⊢ WP cmp_lit #n1 #n2 @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam; wp_pures.
case: (Z.compare_spec n1 n2) => [->|lt|gt].
- by rewrite bool_decide_eq_true_2 //; wp_pures.
- rewrite bool_decide_eq_false_2; last by move=> [=]; lia.
  wp_pures; rewrite bool_decide_eq_true_2 //.
  by wp_pures.
- rewrite bool_decide_eq_false_2; last by move=> [=]; lia.
  wp_pures; rewrite bool_decide_eq_false_2; last lia.
  by wp_pures.
Qed.

Lemma twp_cmp_lit_loc (l1 l2 : loc) E Ψ :
  Ψ #(cmp_Z (Z.compare (loc_car l1) (loc_car l2))) ⊢
  WP cmp_lit #l1 #l2 @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam; wp_pures.
case: (Z.compare_spec (loc_car l1) (loc_car l2)) => [e|lt|gt].
- have -> : l1 = l2 by case: l1 l2 e => [z1] [z2] /= ->.
  by rewrite bool_decide_eq_true_2 //; wp_pures.
- rewrite bool_decide_eq_false_2;
    last by move=> [=] e; move: lt; rewrite e; lia.
  wp_pures; rewrite bool_decide_eq_true_2 //.
  by wp_pures.
- rewrite bool_decide_eq_false_2;
    last by move=> [=] e; move: gt; rewrite e; lia.
  wp_pures; rewrite bool_decide_eq_false_2; last by rewrite /Loc.lt; lia.
  by wp_pures.
Qed.

Lemma twp_cmp_op0 (o1 o2 : term_op0) E Ψ :
  Ψ #(cmp_Z (PreTerm.cmp_ord o1 o2)) ⊢
  WP cmp_op0 (repr o1) (repr o2) @ E [{ Ψ }].
Proof.
rewrite cmp_op0E.
case: o1 o2 => [n1|[l1]] [n2|[l2]] /=; iIntros "HΨ"; wp_lam; wp_pures.
- by wp_apply twp_cmp_lit_int.
- by wp_apply twp_cmp_lit_int.
- by wp_apply twp_cmp_lit_int.
- by wp_apply twp_cmp_lit_loc.
Qed.

Lemma twp_cmp_op1 (o1 o2 : term_op1) E Ψ :
  Ψ #(cmp_Z (PreTerm.cmp_ord o1 o2)) ⊢
  WP cmp_op1 (repr o1) (repr o2) @ E [{ Ψ }].
Proof.
rewrite cmp_op1E.
case: o1 o2 => [k1|] [k2|] /=; iIntros "HΨ"; wp_lam; wp_pures.
- by wp_apply twp_cmp_lit_int.
- by wp_apply twp_cmp_lit_int.
- by wp_apply twp_cmp_lit_int.
- by [].
Qed.

Lemma twp_cmp_op2 (o1 o2 : term_op2) E Ψ :
  Ψ #(cmp_Z (PreTerm.cmp_ord o1 o2)) ⊢
  WP cmp_op2 (repr o1) (repr o2) @ E [{ Ψ }].
Proof.
rewrite cmp_op2E.
by case: o1 o2 => [] [] /=; iIntros "HΨ"; wp_lam; wp_pures;
  wp_apply twp_cmp_lit_int.
Qed.

(** [cmp_spec enc c cv x]: [cv] compares [x], encoded with [enc], as [c]
    does. *)
Definition cmp_spec {A} (enc : A → val) (c : A → A → comparison) (cv : val)
    (x : A) : Prop :=
  ∀ (y : A) E Ψ, Ψ #(cmp_Z (c x y)) ⊢ WP cv (enc x) (enc y) @ E [{ Ψ }].

Lemma twp_cmp_list {A} (enc : A → val) (c : A → A → comparison) (cv : val)
    (xs ys : list A) E Ψ :
  Forall (cmp_spec enc c cv) xs →
  Ψ #(cmp_Z (PreTerm.cmp_list c xs ys)) ⊢
  WP cmp_list cv (repr_list (map enc xs)) (repr_list (map enc ys))
    @ E [{ Ψ }].
Proof.
rewrite [@repr_list]unlock.
elim: xs ys E Ψ => [|x xs IH] [|y ys] E Ψ H /=; iIntros "HΨ";
  wp_rec; wp_pures; try by iApply "HΨ".
have Hx := Forall_inv H; have {}IH := IH ys _ _ (Forall_inv_tail H).
wp_apply Hx; case: (c x y) => /=; wp_pures.
- by iApply IH.
- by iApply "HΨ".
- by iApply "HΨ".
Qed.

Lemma twp_cmp_poly (c : PreTerm.pre_term → PreTerm.pre_term → comparison)
    (cv : val) (A A' : PreTerm.poly_lists) E Ψ :
  PreTerm.poly_all (cmp_spec repr c cv) A →
  Ψ #(cmp_Z (PreTerm.cmp_poly c A A')) ⊢
  WP cmp_poly cv (val_poly val_of_pre_term A)
                 (val_poly val_of_pre_term A') @ E [{ Ψ }].
Proof.
case: A A' => [ps ns] [ps' ns'] [Hps Hns] /=.
have M ms : PreTerm.monos_all (cmp_spec repr c cv) ms →
    Forall (cmp_spec (val_mono val_of_pre_term) (PreTerm.cmp_list c)
              (λ: "m" "n", cmp_list cv "m" "n")) ms.
  apply: PreTerm.monos_all_Forall_impl => m Hm m' E' Φ; iIntros "HΦ".
  wp_pures; iApply (twp_cmp_list with "HΦ"); exact: Hm.
iIntros "HΨ"; rewrite /val_poly /=; wp_lam; wp_pures.
wp_apply (twp_cmp_list _ _ _ ps ps'); first exact: M.
rewrite /PreTerm.cmp_poly /PreTerm.cmp_pair.
case: (PreTerm.cmp_list _ ps ps') => /=; wp_pures.
- by wp_apply (twp_cmp_list _ _ _ ns ns'); first exact: M.
- by iApply "HΨ".
- by iApply "HΨ".
Qed.

Lemma twp_cmp_frac (c : PreTerm.pre_term → PreTerm.pre_term → comparison)
    (cv : val) (F F' : PreTerm.frac_lists) E Ψ :
  PreTerm.frac_all (cmp_spec repr c cv) F →
  Ψ #(cmp_Z (PreTerm.cmp_frac c F F')) ⊢
  WP cmp_frac cv (val_frac val_of_pre_term F)
                 (val_frac val_of_pre_term F') @ E [{ Ψ }].
Proof.
case: F F' => [A B] [A' B'] [HA HB] /=.
iIntros "HΨ"; rewrite /val_frac /=; wp_lam; wp_pures.
wp_apply (twp_cmp_poly _ _ A A'); first exact: HA.
rewrite /PreTerm.cmp_frac /PreTerm.cmp_pair.
case: (PreTerm.cmp_poly _ A A') => /=; wp_pures.
- by wp_apply (twp_cmp_poly _ _ B B').
- by iApply "HΨ".
- by iApply "HΨ".
Qed.

Lemma twp_cmp_term x y E Ψ :
  Ψ #(cmp_Z (PreTerm.pt_cmp x y)) ⊢ WP cmp_term (repr x) (repr y) @ E [{ Ψ }].
Proof.
elim: x y E Ψ => [o1|o1 t1 IH|o1 a1 IHa b1 IHb|F1 IH|l1 IH]
  [o2|o2 t2|o2 a2 b2|F2|l2] E Ψ /=; iIntros "HΨ"; wp_rec; wp_pures;
  try by wp_apply twp_cmp_lit_int.
- by wp_apply twp_cmp_op0.
- wp_apply twp_cmp_op1; case: (PreTerm.cmp_ord o1 o2) => /=; wp_pures.
  + by iApply IH.
  + by iApply "HΨ".
  + by iApply "HΨ".
- wp_apply twp_cmp_op2; case: (PreTerm.cmp_ord o1 o2) => /=; wp_pures.
  + wp_apply IHa; case: (PreTerm.pt_cmp a1 a2) => /=; wp_pures.
    * by iApply IHb.
    * by iApply "HΨ".
    * by iApply "HΨ".
  + by iApply "HΨ".
  + by iApply "HΨ".
- by iApply (twp_cmp_frac with "HΨ").
- wp_apply (twp_cmp_list (λ e, (val_of_pre_term e.1,
                                val_frac val_of_pre_term e.2)%V)
                         (PreTerm.cmp_pair PreTerm.pt_cmp
                            (PreTerm.cmp_frac PreTerm.pt_cmp))); last first.
    by iApply "HΨ".
  have HF F : PreTerm.frac_all (cmp_spec repr PreTerm.pt_cmp cmp_term) F →
      ∀ F' E Ψ, Ψ #(cmp_Z (PreTerm.cmp_frac PreTerm.pt_cmp F F')) ⊢
        WP cmp_frac cmp_term (val_frac val_of_pre_term F)
                             (val_frac val_of_pre_term F') @ E [{ Ψ }].
    by move=> HF F' E' Φ; iIntros "HΦ"; iApply (twp_cmp_frac with "HΦ").
  apply: Forall_impl (PreTerm.entries_all_Forall_impl HF IH) _.
  move=> - [b F] /= [Hb {}HF] [b' F'] E' Φ; iIntros "HΦ".
  wp_pures; wp_lam; wp_pures.
  wp_apply Hb; rewrite /PreTerm.cmp_pair.
  case: (PreTerm.pt_cmp b b') => /=; wp_pures.
  + by iApply HF.
  + by iApply "HΦ".
  + by iApply "HΦ".
Qed.

Lemma twp_eq_pre_term x y E Ψ :
  Ψ #(bool_decide (x = y)) ⊢ WP eq_term (repr x) (repr y) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam; wp_pures; wp_apply twp_cmp_term; wp_pures.
have -> : bool_decide (#(cmp_Z (PreTerm.pt_cmp x y)) = #0) =
          bool_decide (x = y).
  apply: bool_decide_ext; rewrite -PreTerm.pt_cmp_eq.
  by case: (PreTerm.pt_cmp x y); split=> // - [].
by [].
Qed.

Lemma twp_leq_pre_term x y E Ψ :
  Ψ #(bool_decide (MSet.le x y)) ⊢ WP leq_term (repr x) (repr y) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam; wp_pures; wp_apply twp_cmp_term; wp_pures.
have -> : negb (bool_decide (#(cmp_Z (PreTerm.pt_cmp x y)) = #1)) =
          bool_decide (MSet.le x y).
  rewrite -bool_decide_not; apply: bool_decide_ext.
  rewrite /MSet.le lexico_pt_cmp -PreTerm.pt_cmp_eq.
  by case: (PreTerm.pt_cmp x y) => /=; intuition congruence.
by [].
Qed.

(** *** Encodings *)

Lemma repr_mono_car (m : MSet.mset PreTerm.pre_term) :
  repr m = val_mono val_of_pre_term (MSet.car m).
Proof.
rewrite repr_msetE /val_mono; change (elements m) with (MSet.car m).
rewrite [@repr_list]unlock /=.
by elim: (MSet.car m) => //= x xs ->.
Qed.

Lemma repr_monos (ms : list (MSet.mset PreTerm.pre_term)) :
  repr ms = repr_list (map (val_mono val_of_pre_term) (MSet.car <$> ms)).
Proof.
rewrite [@repr_list]unlock /=.
by elim: ms => //= m ms ->; rewrite -[repr_mset m]/(repr m) repr_mono_car.
Qed.

Lemma repr_poly_lists (p : Poly.poly PreTerm.pre_term) :
  repr p = val_poly val_of_pre_term (PreTerm.poly_lists_of p).
Proof. by rewrite repr_polyE repr_smsE repr_pair !repr_msetE !repr_monos. Qed.

Lemma repr_frac_lists (r : Frac.frac PreTerm.pre_term) :
  repr r = val_frac val_of_pre_term (PreTerm.frac_lists_of r).
Proof. by rewrite repr_fracE repr_pair !repr_poly_lists. Qed.

Lemma repr_dhmap (m : PreTerm.dhmap) :
  repr m = repr_list (map (λ e, (val_of_pre_term e.1,
                                  val_frac val_of_pre_term e.2)%V)
                          (PreTerm.entries m)).
Proof.
rewrite repr_fmapE /PreTerm.entries [@repr_list]unlock /=.
elim: (FMap.to_list m) => //= - [b r] l -> /=.
by rewrite -[repr_prod (b, r)]/(repr (b, r)) repr_pair repr_frac_lists.
Qed.

Lemma hl_oneE : hl_one = repr PreTerm.one.
Proof. by rewrite /= /val_frac /val_poly /val_mono [@repr_list]unlock. Qed.

Lemma hl_zeroE : hl_zero = repr (PreTerm.PTMod PreTerm.zero_lists).
Proof. by rewrite /= /val_frac /val_poly /val_mono [@repr_list]unlock. Qed.

Lemma hl_goneE : hl_gone = repr (PreTerm.PTDH []).
Proof. by rewrite /= [@repr_list]unlock. Qed.

(** *** Fractions *)

Lemma twp_eq_frac (f g : Frac.frac PreTerm.pre_term) E Ψ :
  Ψ #(bool_decide (f = g)) ⊢ WP eq_frac (repr f) (repr g) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam; wp_pures.
by wp_apply (twp_frac_eq eq_term twp_eq_pre_term).
Qed.

Lemma twp_add_frac (f g : Frac.frac PreTerm.pre_term) E Ψ :
  Ψ (repr (Frac.add f g)) ⊢ WP add_frac (repr f) (repr g) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam; wp_pures.
by wp_apply (twp_frac_add eq_term leq_term twp_eq_pre_term twp_leq_pre_term).
Qed.

Lemma twp_mul_frac (f g : Frac.frac PreTerm.pre_term) E Ψ :
  Ψ (repr (Frac.mul f g)) ⊢ WP mul_frac (repr f) (repr g) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam; wp_pures.
by wp_apply (twp_frac_mul eq_term leq_term twp_eq_pre_term twp_leq_pre_term).
Qed.

Lemma twp_inv_frac (f : Frac.frac PreTerm.pre_term) E Ψ :
  Ψ (repr (Frac.inv f)) ⊢ WP inv_frac (repr f) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam.
by wp_apply (twp_frac_inv eq_term leq_term twp_eq_pre_term twp_leq_pre_term).
Qed.

Lemma twp_is_one_frac (f : Frac.frac PreTerm.pre_term) E Ψ :
  Ψ #(bool_decide (f = Frac.one)) ⊢ WP is_one_frac (repr f) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam; rewrite -(repr_frac_one (T := PreTerm.pre_term)).
by wp_apply (twp_frac_eq eq_term twp_eq_pre_term).
Qed.

(** *** Pre-terms *)

Lemma twp_hl_is_mod pt E Ψ :
  Ψ #(PreTerm.is_mod pt) ⊢ WP hl_is_mod (repr pt) @ E [{ Ψ }].
Proof. by case: pt => *; iIntros "HΨ"; wp_lam; wp_pures. Qed.

Lemma twp_hl_is_dh pt E Ψ :
  Ψ #(PreTerm.is_dh pt) ⊢ WP hl_is_dh (repr pt) @ E [{ Ψ }].
Proof. by case: pt => *; iIntros "HΨ"; wp_lam; wp_pures. Qed.

Lemma twp_hl_lone_atom (F : PreTerm.frac_lists) E Ψ :
  Ψ (repr (PreTerm.lone_atom F)) ⊢
  WP hl_lone_atom (val_frac val_of_pre_term F) @ E [{ Ψ }].
Proof.
case: F => [[ps ns] [qs rs]].
rewrite /val_frac /val_poly /val_mono [@repr_list]unlock /=.
iIntros "HΨ"; wp_lam; wp_pures.
case: ps => [|p [|? ?]] /=; wp_pures; try (by iApply "HΨ");
  try (by destruct p as [|? [|? ?]]; iApply "HΨ").
case: ns => [|? ?] /=; wp_pures;
  try (by destruct p as [|? [|? ?]]; iApply "HΨ").
case: p => [|x [|? ?]] /=; wp_pures; try by iApply "HΨ".
case: qs => [|q qs] /=; wp_pures; try by iApply "HΨ".
case: q => [|? ?] /=; wp_pures; try by iApply "HΨ".
case: qs => [|? ?] /=; wp_pures; try by iApply "HΨ".
by case: rs => [|? ?] /=; wp_pures; iApply "HΨ".
Qed.

Lemma twp_hl_mod_of_frac (r : Frac.frac PreTerm.pre_term) E Ψ :
  Ψ (repr (PreTerm.mod_of_frac r)) ⊢ WP hl_mod_of_frac (repr r) @ E [{ Ψ }].
Proof.
rewrite repr_frac_lists /PreTerm.mod_of_frac /PreTerm.mod_of_lists.
move: (PreTerm.frac_lists_of r) => F.
case eF: (PreTerm.lone_atom F) => [x|]; iIntros "HΨ"; wp_lam;
  wp_apply twp_hl_lone_atom; rewrite eF /=; wp_pures; by iApply "HΨ".
Qed.

Lemma twp_hl_frac_of pt E Ψ :
  PreTerm.wf pt →
  Ψ (repr (PreTerm.frac_of pt)) ⊢ WP hl_frac_of (repr pt) @ E [{ Ψ }].
Proof.
move=> wf_pt; iIntros "HΨ"; wp_lam; wp_apply twp_hl_is_mod.
case Em: (PreTerm.is_mod pt); wp_pures.
- case: pt wf_pt Em => // F wf_F _; wp_pures.
  have cF : PreTerm.canonical F.
    by move: wf_F => /= /andb_True [/andb_True [_ ?] _].
  iEval (rewrite repr_frac_lists /= PreTerm.frac_lists_ofK //) in "HΨ".
  by iApply "HΨ".
- iEval (rewrite PreTerm.frac_of_var ?Em //) in "HΨ".
  by wp_apply twp_frac_var.
Qed.

Lemma twp_hl_dh_map pt E Ψ :
  PreTerm.wf pt →
  Ψ (repr (PreTerm.dh_map pt)) ⊢ WP hl_dh_map (repr pt) @ E [{ Ψ }].
Proof.
move=> wf_pt.
case Ed: (PreTerm.is_dh pt).
- case: pt wf_pt Ed => // l wf_l _.
  rewrite repr_dhmap /= PreTerm.entries_of_entries //.
  iIntros "HΨ"; wp_lam; wp_apply (twp_hl_is_dh (PreTerm.PTDH l)); wp_pures.
  by iApply "HΨ".
- have -> : PreTerm.dh_map pt = {[pt := Frac.one]} by case: pt Ed {wf_pt}.
  iIntros "HΨ"; wp_lam; wp_apply twp_hl_is_dh; rewrite Ed; wp_pures.
  rewrite -(repr_frac_zero (T := PreTerm.pre_term))
    -(repr_frac_one (T := PreTerm.pre_term)).
  by wp_apply (twp_fmap_singleton Frac.zero eq_frac twp_eq_frac).
Qed.

Lemma twp_hl_dh_of (m : PreTerm.dhmap) E Ψ :
  Ψ (repr (PreTerm.dh_of m)) ⊢ WP hl_dh_of (repr m) @ E [{ Ψ }].
Proof.
have e : repr (PreTerm.PTDH (PreTerm.entries m)) = (#TDH_tag, repr m)%V.
  by rewrite [repr m]repr_dhmap.
case E': (FMap.to_list m) => [|[b r] [|e' l]].
- have -> : PreTerm.dh_of m = PreTerm.PTDH (PreTerm.entries m).
    by rewrite /PreTerm.dh_of E'.
  rewrite e [repr m]repr_fmapE E' repr_nil.
  by iIntros "HΨ"; wp_lam; wp_pures; iApply "HΨ".
- have -> : PreTerm.dh_of m = PreTerm.mk_exp b r.
    by rewrite /PreTerm.dh_of E'.
  have Ee : PreTerm.entries m = [(b, PreTerm.frac_lists_of r)].
    by rewrite /PreTerm.entries E'.
  rewrite Ee [repr m]repr_fmapE E' repr_cons repr_nil repr_pair in e.
  rewrite /PreTerm.mk_exp [repr m]repr_fmapE E' repr_cons repr_nil repr_pair.
  case: bool_decide_reflect => [er|ne].
  + iIntros "HΨ"; wp_lam; wp_pures; wp_apply twp_is_one_frac.
    by rewrite bool_decide_eq_true_2 //; wp_pures; iApply "HΨ".
  + rewrite e; iIntros "HΨ"; wp_lam; wp_pures; wp_apply twp_is_one_frac.
    by rewrite bool_decide_eq_false_2 //; wp_pures; iApply "HΨ".
- have -> : PreTerm.dh_of m = PreTerm.PTDH (PreTerm.entries m).
    by rewrite /PreTerm.dh_of E'.
  rewrite e [repr m]repr_fmapE E' !repr_cons.
  by iIntros "HΨ"; wp_lam; wp_pures; iApply "HΨ".
Qed.

Lemma twp_hl_dh_add (m1 m2 : PreTerm.dhmap) E Ψ :
  Ψ (repr (PreTerm.dh_add m1 m2)) ⊢
  WP hl_dh_add (repr m1) (repr m2) @ E [{ Ψ }].
Proof.
rewrite /PreTerm.dh_add repr_fmapE FMap.to_list_cast -repr_fmapE.
iIntros "HΨ"; wp_lam; wp_pures;
  rewrite -(repr_frac_zero (T := PreTerm.pre_term)).
wp_apply (twp_fmap_merge eq_term leq_term twp_eq_pre_term twp_leq_pre_term
            Frac.zero Frac.zero eq_frac twp_eq_frac Frac.add); last done.
move=> a b E' Φ; iIntros "HΦ"; by wp_apply twp_add_frac.
Qed.

Lemma twp_hl_dh_opp (m : PreTerm.dhmap) E Ψ :
  Ψ (repr (PreTerm.dh_opp m)) ⊢ WP hl_dh_opp (repr m) @ E [{ Ψ }].
Proof.
rewrite /PreTerm.dh_opp repr_fmapE FMap.to_list_cast -repr_fmapE.
iIntros "HΨ"; wp_lam; rewrite -(repr_frac_zero (T := PreTerm.pre_term)).
wp_apply (twp_fmap_map Frac.zero eq_frac twp_eq_frac Frac.opp); last done.
move=> a E' Φ; iIntros "HΦ"; by wp_apply twp_frac_opp.
Qed.

Lemma twp_hl_dh_scale (r : Frac.frac PreTerm.pre_term) (m : PreTerm.dhmap)
    E Ψ :
  Ψ (repr (PreTerm.dh_scale r m)) ⊢
  WP hl_dh_scale (repr r) (repr m) @ E [{ Ψ }].
Proof.
rewrite /PreTerm.dh_scale repr_fmapE FMap.to_list_cast -repr_fmapE.
iIntros "HΨ"; wp_lam; wp_pures;
  rewrite -(repr_frac_zero (T := PreTerm.pre_term)).
wp_apply (twp_fmap_map Frac.zero eq_frac twp_eq_frac
            (λ f, Frac.mul f r)); last done.
move=> a E' Φ; iIntros "HΦ"; wp_pures; by wp_apply twp_mul_frac.
Qed.

(** *** Operations *)

Lemma twp_hl_mul pt1 pt2 E Ψ :
  PreTerm.wf pt1 → PreTerm.wf pt2 →
  Ψ (repr (PreTerm.mul {[+ pt1; pt2 +]})) ⊢
  WP hl_mul (repr pt1) (repr pt2) @ E [{ Ψ }].
Proof.
move=> wf1 wf2; rewrite /PreTerm.mul Frac.sprod_pair.
iIntros "HΨ"; wp_lam; wp_pures.
wp_apply (twp_hl_frac_of pt2 _ _ wf2); wp_apply (twp_hl_frac_of pt1 _ _ wf1).
by wp_apply twp_mul_frac; wp_apply twp_hl_mod_of_frac.
Qed.

Lemma twp_hl_inv pt E Ψ :
  PreTerm.wf pt →
  Ψ (repr (PreTerm.mul (SMS.inv {[+ pt +]}))) ⊢
  WP hl_inv (repr pt) @ E [{ Ψ }].
Proof.
move=> wf_pt; rewrite /PreTerm.mul Frac.sprod_inv Frac.sprod_singleton.
iIntros "HΨ"; wp_lam; wp_apply (twp_hl_frac_of pt _ _ wf_pt).
by wp_apply twp_inv_frac; wp_apply twp_hl_mod_of_frac.
Qed.

Lemma twp_hl_sum pt1 pt2 E Ψ :
  PreTerm.wf pt1 → PreTerm.wf pt2 →
  Ψ (repr (PreTerm.sum {[+ pt1; pt2 +]})) ⊢
  WP hl_sum (repr pt1) (repr pt2) @ E [{ Ψ }].
Proof.
move=> wf1 wf2.
rewrite /PreTerm.sum Frac.ssum_disj_union !Frac.ssum_singleton.
iIntros "HΨ"; wp_lam; wp_pures.
wp_apply (twp_hl_frac_of pt2 _ _ wf2); wp_apply (twp_hl_frac_of pt1 _ _ wf1).
by wp_apply twp_add_frac; wp_apply twp_hl_mod_of_frac.
Qed.

Lemma twp_hl_opp pt E Ψ :
  PreTerm.wf pt →
  Ψ (repr (PreTerm.sum (SMS.inv {[+ pt +]}))) ⊢
  WP hl_opp (repr pt) @ E [{ Ψ }].
Proof.
move=> wf_pt; rewrite /PreTerm.sum Frac.ssum_inv Frac.ssum_singleton.
iIntros "HΨ"; wp_lam; wp_apply (twp_hl_frac_of pt _ _ wf_pt).
by wp_apply twp_frac_opp; wp_apply twp_hl_mod_of_frac.
Qed.

Lemma twp_hl_gmul pt1 pt2 E Ψ :
  PreTerm.wf pt1 → PreTerm.wf pt2 →
  Ψ (repr (PreTerm.gmul {[+ pt1; pt2 +]})) ⊢
  WP hl_gmul (repr pt1) (repr pt2) @ E [{ Ψ }].
Proof.
move=> wf1 wf2; rewrite /PreTerm.gmul PreTerm.dh_sum_pair.
iIntros "HΨ"; wp_lam; wp_pures.
wp_apply (twp_hl_dh_map pt2 _ _ wf2); wp_apply (twp_hl_dh_map pt1 _ _ wf1).
by wp_apply twp_hl_dh_add; wp_apply twp_hl_dh_of.
Qed.

Lemma twp_hl_ginv pt E Ψ :
  PreTerm.wf pt →
  Ψ (repr (PreTerm.gmul (SMS.inv {[+ pt +]}))) ⊢
  WP hl_ginv (repr pt) @ E [{ Ψ }].
Proof.
move=> wf_pt; rewrite /PreTerm.gmul PreTerm.dh_sum_inv_singleton.
iIntros "HΨ"; wp_lam; wp_apply (twp_hl_dh_map pt _ _ wf_pt).
by wp_apply twp_hl_dh_opp; wp_apply twp_hl_dh_of.
Qed.

Lemma twp_hl_exp b e E Ψ :
  PreTerm.wf b → PreTerm.wf e →
  Ψ (repr (PreTerm.exp b e)) ⊢ WP hl_exp (repr b) (repr e) @ E [{ Ψ }].
Proof.
move=> wf_b wf_e; rewrite /PreTerm.exp /PreTerm.exp_frac.
iIntros "HΨ"; wp_lam; wp_pures.
wp_apply (twp_hl_dh_map b _ _ wf_b); wp_apply (twp_hl_frac_of e _ _ wf_e).
by wp_apply twp_hl_dh_scale; wp_apply twp_hl_dh_of.
Qed.

End Proofs.
