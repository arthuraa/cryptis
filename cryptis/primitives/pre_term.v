(* HeapLang implementations of the pre-term operations of
   [core/pre_term/normalize.v], together with specs saying that each program
   computes the corresponding pure function.

   Every pure function of [normalize.v] has a counterpart here:

     is_exp / is_mul / is_gmul / is_nonce  ->  hl_is_exp / hl_is_mul /
                                               hl_is_gmul / hl_is_nonce
     base / expo                           ->  hl_base / hl_expo
     factors / gfactors / dh_factors       ->  hl_factors / hl_gfactors /
                                               hl_dh_factors
     mul_aux / gmul_aux / dh_of            ->  hl_mul_aux / hl_gmul_aux /
                                               hl_dh_of
     SMS.bind factors / SMS.bind gfactors  ->  hl_normalize_factors /
                                               hl_normalize_gfactors
     mul / gmul                            ->  hl_mul_pair / hl_gmul_pair
     mk_exp / exp_aux / exp                ->  hl_mk_exp / hl_exp_aux / hl_exp

   Pairs of lists are represented as HeapLang pairs ([repr_prod]).
   [hl_mul]/[hl_inv] (and [hl_gmul]/[hl_ginv]) are [hl_mul_pair] at
   [([t1; t2], [])] and [([], [t])].

   [normalize] itself is not implemented: the HeapLang layer only ever builds
   pre-terms with the smart constructors, so it never needs to renormalise.

   The product machinery is not reimplemented here.  [SMS.bind factors] of
   two lists is [SMS.make] of their flattened factor lists ([bind_flat]), so
   [hl_normalize_factors] flattens them with [hl_flat], sorts both sides with
   [mset_of_list] and cancels them with [sms_to] from [primitives/sms.v].
   [hl_gmul_aux] adds the group factors one at a time to a map from bases to
   logarithms ([PreTerm.gmul_auxE]), with the operations of
   [primitives/fmap.v].

   These proofs take much longer to check than the rest of the development.
   Since they don't have many dependencies, they are left in their own file to
   avoid slowing down the compilation process. *)

From mathcomp Require Import ssreflect.
From stdpp Require Import list sorting lexico.
From iris.heap_lang Require Import notation proofmode.
From cryptis.lib Require Import repr list list_sort fmap mset sms.
From cryptis.core Require Import pre_term.
From cryptis.primitives Require Import mset sms fmap.

Unset Printing Implicit Defensive.

#[local] Abbreviation entry :=
  (PreTerm.pre_term * (list PreTerm.pre_term * list PreTerm.pre_term))%type.

(** ** Structural equality *)

Definition eq_term_op0 : val := λ: "x" "y",
  (Fst "x" = Fst "y") && (Snd "x" = Snd "y").

Definition eq_key_type : val := λ: "x" "y",
  "x" = "y".

Definition eq_term_op1 : val := λ: "x" "y",
  if: (Fst "x" = Fst "y") then
    let: "tag" := Fst "x" in
    if: "tag" = #TKey_tag then
      eq_key_type (Snd "x") (Snd "y")
    else (* Hash *) #true
  else #false.

Definition eq_term_op2 : val := λ: "x" "y",
  "x" = "y".

Definition eq_term : val := (rec: "eq" "x" "y" :=
  if: (Fst "x" = Fst "y") then
    let: "tag" := Fst "x" in
    if: "tag" = #TOp0_tag then
      eq_term_op0 (Snd "x") (Snd "y")
    else if: "tag" = #TOp1_tag then
      eq_term_op1 (Fst (Snd "x")) (Fst (Snd "y")) &&
      "eq" (Snd (Snd "x")) (Snd (Snd "y"))
    else if: "tag" = #TOp2_tag then
      eq_term_op2 (Fst (Fst (Snd "x"))) (Fst (Fst (Snd "y"))) &&
      "eq" (Snd (Fst (Snd "x"))) (Snd (Fst (Snd "y"))) &&
      "eq" (Snd (Snd "x")) (Snd (Snd "y"))
    else if: "tag" = #TMul_tag then
      eq_list "eq" (Fst (Snd "x")) (Fst (Snd "y")) &&
      eq_list "eq" (Snd (Snd "x")) (Snd (Snd "y"))
    else if: "tag" = #TDH_tag then
      eq_list (λ: "e1" "e2",
                 "eq" (Fst "e1") (Fst "e2") &&
                 eq_list "eq" (Fst (Snd "e1")) (Fst (Snd "e2")) &&
                 eq_list "eq" (Snd (Snd "e1")) (Snd (Snd "e2")))
        (Snd "x") (Snd "y")
    else #false
  else #false)%V.

Definition eq_entry : val := λ: "e1" "e2",
  eq_term (Fst "e1") (Fst "e2") &&
  eq_list eq_term (Fst (Snd "e1")) (Fst (Snd "e2")) &&
  eq_list eq_term (Snd (Snd "e1")) (Snd (Snd "e2")).

(** ** The derived total order *)

Definition leq_term_op0 : val := λ: "x" "y",
  if: (Fst "x" < Fst "y") then #true
  else if: (Fst "x" = Fst "y") then Snd "x" ≤ Snd "y"
  else #false.

Definition leq_key_type : val := λ: "x" "y",
  "x" ≤ "y".

Definition leq_term_op1 : val := λ: "x" "y",
  if: (Fst "x" < Fst "y") then #true
  else if: (Fst "x" = Fst "y") then
    if: Fst "x" = #TKey_tag then leq_key_type (Snd "x") (Snd "y")
    else #true (* Hash *)
  else #false.

Definition leq_term_op2 : val := λ: "x" "y",
  "x" ≤ "y".

Definition leq_term : val := (rec: "loop" "t1" "t2" :=
  if: (Fst "t1" < Fst "t2") then #true
  else if: (Fst "t1" = Fst "t2") then
    let: "tag" := Fst "t1" in
    let: "a1"  := Snd "t1" in
    let: "a2"  := Snd "t2" in
    if: "tag" = #TOp0_tag then
      leq_term_op0 "a1" "a2"
    else if: "tag" = #TOp1_tag then
      let: "o1" := Fst "a1" in
      let: "o2" := Fst "a2" in
      if: eq_term_op1 "o1" "o2" then "loop" (Snd "a1") (Snd "a2")
      else leq_term_op1 "o1" "o2"
    else if: "tag" = #TOp2_tag then
      let: "o1" := Fst (Fst "a1") in
      let: "o2" := Fst (Fst "a2") in
      if: eq_term_op2 "o1" "o2" then
        (if: eq_term (Snd (Fst "a1")) (Snd (Fst "a2"))
         then "loop" (Snd "a1") (Snd "a2")
         else "loop" (Snd (Fst "a1")) (Snd (Fst "a2")))
      else leq_term_op2 "o1" "o2"
    else if: "tag" = #TMul_tag then
      if: eq_list eq_term (Fst "a1") (Fst "a2")
      then leq_list eq_term "loop" (Snd "a1") (Snd "a2")
      else leq_list eq_term "loop" (Fst "a1") (Fst "a2")
    else if: "tag" = #TDH_tag then
      leq_list eq_entry
        (λ: "e1" "e2",
           if: eq_term (Fst "e1") (Fst "e2") then
             (if: eq_list eq_term (Fst (Snd "e1")) (Fst (Snd "e2"))
              then leq_list eq_term "loop" (Snd (Snd "e1")) (Snd (Snd "e2"))
              else leq_list eq_term "loop" (Fst (Snd "e1")) (Fst (Snd "e2")))
           else "loop" (Fst "e1") (Fst "e2"))
        "a1" "a2"
    else #false
  else #false)%V.

(** ** Recognisers *)

Definition hl_is_exp : val := λ: "pt",
  if: Fst "pt" = #TDH_tag then
    match: Snd "pt" with
      NONE => #false
    | SOME "c" =>
      match: Snd "c" with
        NONE =>
          match: Fst (Snd (Fst "c")) with
            NONE => #false
          | SOME "d" =>
            match: Snd "d" with
              NONE =>
                match: Snd (Snd (Fst "c")) with
                  NONE => #true
                | SOME <> => #false
                end
            | SOME <> => #false
            end
          end
      | SOME <> => #false
      end
    end
  else #false.

Definition hl_is_mul : val := λ: "pt", Fst "pt" = #TMul_tag.

Definition hl_is_gmul : val := λ: "pt",
  if: Fst "pt" = #TDH_tag then ~ hl_is_exp "pt" else #false.

Definition hl_is_nonce : val := λ: "pt",
  if: Fst "pt" = #TOp0_tag then Fst (Snd "pt") = #TNonce_tag else #false.

(** ** Destructors *)

(* [repr (PreTerm.PTMul [] [])], i.e. the unit of the product. *)
Definition hl_one : val := (#TMul_tag, (NILV, NILV))%V.

Definition hl_gone : val := (#TDH_tag, NILV)%V.

Definition hl_base : val := λ: "pt",
  if: hl_is_exp "pt" then
    match: Snd "pt" with NONE => "pt" | SOME "c" => Fst (Fst "c") end
  else "pt".

Definition hl_expo : val := λ: "pt",
  if: hl_is_exp "pt" then
    match: Snd "pt" with
      NONE => hl_one
    | SOME "c" =>
      match: Fst (Snd (Fst "c")) with NONE => hl_one | SOME "d" => Fst "d" end
    end
  else hl_one.

Definition hl_factors : val := λ: "pt",
  if: hl_is_mul "pt" then Snd "pt" else ("pt" :: NILV, NILV).

Definition hl_mk_exp : val := λ: "b" "e",
  if: eq_term "e" hl_one then "b"
  else (#TDH_tag, ("b", ("e" :: NILV, NILV)) :: NILV).

Definition hl_dh_factors : val := λ: "l",
  foldr_list
    (λ: "e" "acc",
       let: "f" := (λ: "p", hl_mk_exp (Fst "e") "p") in
       sms_disj_union eq_term leq_term
         (sms_map eq_term leq_term "f" (Snd "e")) "acc")
    (NILV, NILV) "l".

Definition hl_gfactors : val := λ: "pt",
  if: hl_is_gmul "pt" then hl_dh_factors (Snd "pt")
  else ("pt" :: NILV, NILV).

(** ** Smart constructors *)

Definition hl_mul_aux : val := λ: "A",
  match: Fst "A" with
    NONE => (#TMul_tag, "A")
  | SOME "x" =>
      match: Snd "x" with
        NONE =>
          match: Snd "A" with
            NONE => Fst "x"
          | SOME <> => (#TMul_tag, "A")
          end
      | SOME <> => (#TMul_tag, "A")
      end
  end.

Definition hl_dh_of : val := λ: "m",
  match: "m" with
    NONE => (#TDH_tag, "m")
  | SOME "c" =>
    match: Snd "c" with
      NONE =>
        let: "v" := Snd (Fst "c") in
        match: Fst "v" with
          NONE => (#TDH_tag, "m")
        | SOME "d" =>
          match: Snd "d" with
            NONE =>
              match: Snd "v" with
                NONE => hl_mk_exp (Fst (Fst "c")) (Fst "d")
              | SOME <> => (#TDH_tag, "m")
              end
          | SOME <> => (#TDH_tag, "m")
          end
        end
    | SOME <> => (#TDH_tag, "m")
    end
  end.

(* Adds ["sgn" (expo "t")] to the logarithm of [base "t"] in the map ["m"]. *)
Definition hl_curry_add : val := λ: "sgn" "t" "m",
  let: "b" := hl_base "t" in
  let: "v" := fmap_lookup eq_term (NILV, NILV) "b" "m" in
  fmap_insert eq_term leq_term (λ: "s1" "s2", sms_eq eq_term "s1" "s2")
    (NILV, NILV) "b"
    (sms_disj_union eq_term leq_term "v" ("sgn" (hl_expo "t"))) "m".

Definition hl_gmul_aux : val := λ: "A",
  let: "pos" := (λ: "x", ("x" :: NILV, NILV)) in
  let: "neg" := (λ: "x", (NILV, "x" :: NILV)) in
  let: "m" :=
    foldr_list (λ: "t" "m", hl_curry_add "neg" "t" "m") fmap_empty (Snd "A") in
  hl_dh_of
    (foldr_list (λ: "t" "m", hl_curry_add "pos" "t" "m") "m" (Fst "A")).

(* [mbind (λ t, (f t).1)] and [mbind (λ t, (f t).2)]. *)
Definition hl_bind_fst : val := λ: "f" "l",
  foldr_list (λ: "t" "acc", append_lists (Fst ("f" "t")) "acc") [] "l".

Definition hl_bind_snd : val := λ: "f" "l",
  foldr_list (λ: "t" "acc", append_lists (Snd ("f" "t")) "acc") [] "l".

Definition hl_flat : val := λ: "f" "A",
  (append_lists (hl_bind_fst "f" (Fst "A")) (hl_bind_snd "f" (Snd "A")),
   append_lists (hl_bind_snd "f" (Fst "A")) (hl_bind_fst "f" (Snd "A"))).

Definition hl_normalize_factors : val := λ: "A",
  let: "B" := hl_flat hl_factors "A" in
  sms_to eq_term (mset_of_list leq_term (Fst "B"))
    (mset_of_list leq_term (Snd "B")).

Definition hl_normalize_gfactors : val := λ: "A",
  let: "B" := hl_flat hl_gfactors "A" in
  sms_to eq_term (mset_of_list leq_term (Fst "B"))
    (mset_of_list leq_term (Snd "B")).

Definition hl_mul_pair : val := λ: "A",
  hl_mul_aux (hl_normalize_factors "A").

Definition hl_gmul_pair : val := λ: "A",
  hl_gmul_aux (hl_normalize_gfactors "A").

Definition hl_mul : val := λ: "t1" "t2",
  hl_mul_pair ("t1" :: "t2" :: NILV, NILV).

Definition hl_gmul : val := λ: "t1" "t2",
  hl_gmul_pair ("t1" :: "t2" :: NILV, NILV).

Definition hl_inv : val := λ: "t", hl_mul_pair (NILV, "t" :: NILV).

Definition hl_ginv : val := λ: "t", hl_gmul_pair (NILV, "t" :: NILV).

Definition hl_exp_aux : val := λ: "b" "e",
  hl_mk_exp (hl_base "b") (hl_mul_pair (hl_expo "b" :: "e" :: NILV, NILV)).

(* [exp] spreads [exp_aux] over the group factors. *)
Definition hl_exp : val := λ: "b" "e",
  let: "A" := hl_gfactors "b" in
  let: "f" := (λ: "t", hl_exp_aux "t" "e") in
  hl_gmul_pair (map_list "f" (Fst "A"), map_list "f" (Snd "A")).

Definition texp : val := λ: "base" "exp", hl_exp "base" "exp".

Lemma repr_dhE (l : list entry) :
  repr (PreTerm.PTDH l) = (#TDH_tag, repr l)%V.
Proof.
rewrite /=; congr (_, _)%V; rewrite [RHS]repr_list_val; congr repr_list.
by apply: map_ext => -[b [ps ns]] /=; rewrite -!repr_list_val.
Qed.

(* The same, for goals where [wp_lam] has unfolded [repr]. *)
Lemma val_dhE (l : list entry) :
  val_of_pre_term (PreTerm.PTDH l) = (#TDH_tag, repr l)%V.
Proof. exact: repr_dhE. Qed.

Lemma bool_decide_lexico_prod {A B : Type}
    `{EqDecision A, EqDecision B, Lexico A, Lexico B,
      !StrictOrder (@lexico A _), !TrichotomyT (@lexico A _),
      !StrictOrder (@lexico B _), !TrichotomyT (@lexico B _)}
    (a1 a2 : A) (b1 b2 : B) :
  bool_decide ((a1, b1) = (a2, b2) ∨ lexico (a1, b1) (a2, b2)) =
  if bool_decide (a1 = a2) then bool_decide (b1 = b2 ∨ lexico b1 b2)
  else bool_decide (a1 = a2 ∨ lexico a1 a2).
Proof.
have E : lexico (a1, b1) (a2, b2) ↔
         lexico a1 a2 ∨ a1 = a2 ∧ lexico b1 b2 by [].
move: E; case: (bool_decide_reflect (a1 = a2)) => [<-|ne] E;
  apply: bool_decide_ext; rewrite E; split.
- case=> [[->]|[l|[_ l]]]; [by left|by case: (irreflexivity _ _ l)|by right].
- by case=> [->|l]; [left|right; right].
- by case=> [[e _]|[l|[e _]]]; [|right|].
- by case=> [e|l]; [|right; left].
Qed.

#[local] Lemma bool_decide_entry_eq (b1 b2 : PreTerm.pre_term)
    (p1 n1 p2 n2 : list PreTerm.pre_term) :
  bool_decide ((b1, (p1, n1)) = (b2, (p2, n2))) =
  bool_decide (b1 = b2) && bool_decide (p1 = p2) && bool_decide (n1 = n2).
Proof.
case: (bool_decide_reflect (b1 = b2)) => [->|nb] /=; last first.
  by rewrite bool_decide_eq_false_2 //; case.
case: (bool_decide_reflect (p1 = p2)) => [->|np] /=; last first.
  by rewrite bool_decide_eq_false_2 //; case.
case: (bool_decide_reflect (n1 = n2)) => [->|nn] /=; last first.
  by rewrite bool_decide_eq_false_2 //; case.
by rewrite bool_decide_eq_true_2.
Qed.

#[local] Lemma repr_cons {A} `{!Repr A} (x : A) (xs : list A) :
  repr (x :: xs) = SOMEV (repr x, repr xs).
Proof. by rewrite repr_listE. Qed.

#[local] Lemma repr_fmap_list {A B} `{!Repr A, !Repr B} (f : A → B)
    (l : list A) :
  (∀ x, repr (f x) = repr x) → repr (f <$> l) = repr l.
Proof.
move=> fE; elim: l => [|x l IH]; first by rewrite !repr_listE.
by rewrite fmap_cons !repr_cons IH fE.
Qed.

#[local] Lemma mapE {T U} (f : T → U) (l : list T) : map f l = f <$> l.
Proof. by elim: l => [//|x l IH] /=; rewrite IH. Qed.

Section Proofs.

Context `{!heapGS Σ}.

Implicit Types E : coPset.
Implicit Types pt : PreTerm.pre_term.
Implicit Types v : val.
Implicit Types Ψ : val → iProp Σ.

(** ** Equality *)

Lemma twp_eq_term_op0 E (o1 o2 : term_op0) :
  ⊢ WP (eq_term_op0 (repr o1) (repr o2)) @ E
    [{ v, ⌜v = #(bool_decide (o1 = o2))⌝}].
Proof.
case: o1 o2 => [n1|[a1]] [n2|[a2]] /=; wp_lam; wp_pures => //.
- iPureIntro. congr (# (LitBool _)). apply: bool_decide_ext.
  intuition congruence.
- iPureIntro. congr (# (LitBool _)). apply: bool_decide_ext.
  intuition congruence.
Qed.

Lemma twp_eq_key_type E (o1 o2 : key_type) :
  ⊢ WP (eq_key_type (repr o1) (repr o2)) @ E
    [{ v, ⌜v = #(bool_decide (o1 = o2))⌝}].
Proof. case: o1 o2 => [] [] /=; wp_lam; wp_pures => //. Qed.

Lemma twp_eq_term_op1 E (o1 o2 : term_op1) :
  ⊢ WP (eq_term_op1 (repr o1) (repr o2)) @ E
    [{ v, ⌜v = #(bool_decide (o1 = o2))⌝}].
Proof.
case: o1 o2 => [o1|] [o2|] /=. all: wp_lam; wp_pures => //.
iApply twp_wand; first wp_apply twp_eq_key_type.
iIntros (?) "->". iPureIntro.
congr (# (LitBool _)). apply: bool_decide_ext.
intuition congruence.
Qed.

Lemma twp_eq_term_op2 E (o1 o2 : term_op2) :
  ⊢ WP (eq_term_op2 (repr o1) (repr o2)) @ E
    [{ v, ⌜v = #(bool_decide (o1 = o2))⌝}].
Proof. case: o1 o2 => [] [] /=; wp_lam; wp_pures => //. Qed.

#[local] Definition eq_term_spec E pt1 : Prop :=
  ∀ pt2, ⊢ WP (eq_term (repr pt1) (repr pt2)) @ E
              [{ v, ⌜v = #(bool_decide (pt1 = pt2))⌝ }].

Lemma twp_eq_pre_term_aux E pt1 pt2 :
  ⊢ WP (eq_term (repr pt1) (repr pt2)) @ E
       [{ v, ⌜v = #(bool_decide (pt1 = pt2))⌝ }].
Proof.
have IHl (ts : list PreTerm.pre_term) :
    Forall (eq_term_spec E) ts →
    ∀ x1 x2 Ψ, x1 ∈ ts →
      Ψ #(bool_decide (x1 = x2)) -∗
      WP eq_term (repr x1) (repr x2) @ E [{ Ψ }].
  move=> /Forall_forall IH x1 x2 Ψ /IH {}IH; iIntros "post".
  iApply twp_wand; first iApply IH; by iIntros (?) "->".
move: pt2.
elim: pt1 => [o1|o1 t1 IH1|o1 t11 IH1 t12 IH2
             |ps1 /(PreTerm.foldr_Forall _ _) IHps1
                  ns1 /(PreTerm.foldr_Forall _ _) IHns1
             |l1 /(PreTerm.foldr_Forall_entries _ _) IHl1];
case=> [o2|o2 t2|o2 t21 t22|ps2 ns2|l2]; rewrite ?repr_dhE;
wp_rec; wp_pures=> //.
- iApply twp_wand; first by wp_apply twp_eq_term_op0.
  iIntros (?) "->". iPureIntro; congr (# (LitBool _)).
  apply: bool_decide_ext; intuition congruence.
- wp_bind (eq_term_op1 _ _).
  iApply twp_wand; first by wp_apply twp_eq_term_op1.
  iIntros (?) "->". case: bool_decide_reflect=> e1.
  + wp_pures. iApply twp_wand; first by wp_apply IH1.
    iIntros (?) "->". iPureIntro; congr (# (LitBool _)).
    apply: bool_decide_ext; intuition congruence.
  + wp_pures; iPureIntro; congr (# (LitBool _)).
    rewrite bool_decide_false; congruence.
- wp_bind (eq_term_op2 _ _).
  iApply twp_wand; first by wp_apply twp_eq_term_op2.
  iIntros (?) "->". case: bool_decide_reflect=> e1; last first.
    wp_pures; iPureIntro; congr (# (LitBool _)).
    rewrite bool_decide_false; congruence.
  wp_pures. wp_bind (eq_term _ _).
  wp_apply twp_wand; first by wp_apply IH1.
  iIntros (?) "->". case: bool_decide_reflect=> e2.
    wp_pures. wp_bind (eq_term _ _).
    wp_apply twp_wand; first by wp_apply IH2.
    iIntros (?) "->". iPureIntro; congr (# (LitBool _)).
    by apply: bool_decide_ext; intuition congruence.
  wp_pures; iPureIntro; congr (# (LitBool _)).
  rewrite bool_decide_false; congruence.
- rewrite -!repr_list_val.
  wp_bind (eq_list _ _ _).
  iApply (twp_eq_list (A := PreTerm.pre_term) _ _ _ _ _ (IHl _ IHps1)).
  case: (bool_decide_reflect (ps1 = ps2)) => eP; wp_pures; last first.
    by iPureIntro; congr (# (LitBool _)); rewrite bool_decide_false; congruence.
  iApply (twp_eq_list (A := PreTerm.pre_term) _ _ _ _ _ (IHl _ IHns1)).
  iPureIntro; congr (# (LitBool _)); apply: bool_decide_ext.
  by split; congruence.
- iApply (twp_eq_list (A := entry)).
    move=> e1 e2 Φ e1_in; iIntros "post".
    have := proj1 (Forall_forall _ _) IHl1 e1 e1_in.
    case: e1 e2 {e1_in} => [b1 [p1 n1]] [b2 [p2 n2]] /= [IHb [IHp IHn]].
    rewrite /repr_prod /= bool_decide_entry_eq; wp_pures.
    wp_bind (eq_term _ _); iApply twp_wand; first iApply IHb.
    iIntros (?) "->".
    case: (bool_decide (b1 = b2)); wp_pures; last by iApply "post".
    wp_bind (eq_list _ _ _).
    iApply (twp_eq_list (A := PreTerm.pre_term) _ _ _ _ _ (IHl _ IHp)).
    case: (bool_decide (p1 = p2)); wp_pures; last by iApply "post".
    by iApply (twp_eq_list (A := PreTerm.pre_term) _ _ _ _ _ (IHl _ IHn)).
  iPureIntro; congr (# (LitBool _)); apply: bool_decide_ext.
  by split; congruence.
Qed.

(* Continuation form, with the argument order the [primitives/sms.v]
   hypotheses expect. *)
Lemma twp_eq_pre_term pt1 pt2 E Ψ :
  Ψ #(bool_decide (pt1 = pt2)) ⊢
  WP (eq_term (repr pt1) (repr pt2)) @ E [{ Ψ }].
Proof.
iIntros "H".
iApply twp_wand; first iApply twp_eq_pre_term_aux.
by iIntros (?) "->".
Qed.

Lemma twp_eq_entry (e1 e2 : entry) E Ψ :
  Ψ #(bool_decide (e1 = e2)) ⊢
  WP (eq_entry (repr e1) (repr e2)) @ E [{ Ψ }].
Proof.
case: e1 e2 => [b1 [p1 n1]] [b2 [p2 n2]]; iIntros "post".
rewrite /repr_prod /= bool_decide_entry_eq; wp_lam; wp_pures.
wp_bind (eq_term _ _); iApply twp_eq_pre_term.
case: (bool_decide (b1 = b2)); wp_pures; last by iApply "post".
wp_bind (eq_list _ _ _); iApply (twp_eq_list (A := PreTerm.pre_term)).
  by move=> ? ? ? _; iIntros "H"; iApply twp_eq_pre_term.
case: (bool_decide (p1 = p2)); wp_pures; last by iApply "post".
iApply (twp_eq_list (A := PreTerm.pre_term)); last by iApply "post".
by move=> ? ? ? _; iIntros "H"; iApply twp_eq_pre_term.
Qed.

(** ** Order *)

Lemma twp_leq_key_type E (k1 k2 : key_type) :
  ⊢ WP (leq_key_type (repr k1) (repr k2)) @ E [{ v, ⌜v = #(kt_le k1 k2)⌝}].
Proof. by case: k1 k2 => [] [] /=; wp_lam; wp_pures. Qed.

Lemma twp_leq_term_op0 E (o1 o2 : term_op0) :
  ⊢ WP (leq_term_op0 (repr o1) (repr o2)) @ E [{ v, ⌜v = #(op0_le o1 o2)⌝}].
Proof. by case: o1 o2 => [n1|[l1]] [n2|[l2]] /=; wp_lam; wp_pures. Qed.

Lemma twp_leq_term_op1 E (o1 o2 : term_op1) :
  ⊢ WP (leq_term_op1 (repr o1) (repr o2)) @ E [{ v, ⌜v = #(op1_le o1 o2)⌝}].
Proof.
case: o1 o2 => [k1|] [k2|] /=; wp_lam; wp_pures => //.
iApply twp_wand; first by wp_apply twp_leq_key_type.
by iIntros (?) "->".
Qed.

Lemma twp_leq_term_op2 E (o1 o2 : term_op2) :
  ⊢ WP (leq_term_op2 (repr o1) (repr o2)) @ E [{ v, ⌜v = #(op2_le o1 o2)⌝}].
Proof. by case: o1 o2 => [] [] /=; wp_lam; wp_pures. Qed.

#[local] Definition leq_term_spec E pt1 : Prop :=
  ∀ pt2 Ψ, Ψ #(bool_decide (pt_order pt1 pt2)) ⊢
           WP (leq_term (repr pt1) (repr pt2)) @ E [{ Ψ }].

Lemma twp_leq_pre_term pt1 pt2 E Ψ :
  Ψ #(bool_decide (pt_order pt1 pt2)) ⊢
  WP (leq_term (repr pt1) (repr pt2)) @ E [{ Ψ }].
Proof.
have feqP (x1 x2 : PreTerm.pre_term) :
    [[{ True }]] eq_term (repr x1) (repr x2) @ E
    [[{ RET #(bool_decide (x1 = x2)); True }]].
  by iIntros "%Φ _ post"; iApply twp_eq_pre_term; iApply "post".
have feqP' (x1 x2 : entry) :
    [[{ True }]] eq_entry (repr x1) (repr x2) @ E
    [[{ RET #(bool_decide (x1 = x2)); True }]].
  by iIntros "%Φ _ post"; iApply twp_eq_entry; iApply "post".
have IHl (ts : list PreTerm.pre_term) :
    Forall (leq_term_spec E) ts →
    ∀ x1 x2 : PreTerm.pre_term, x1 ∈ ts →
    [[{ True }]] leq_term (repr x1) (repr x2) @ E
    [[{ RET #(bool_decide (x1 = x2 ∨ lexico x1 x2)); True }]].
  move=> /Forall_forall IH x1 x2 /IH {}IH Φ; iIntros "_ post".
  iApply IH; rewrite (bool_decide_ext _ _ (pt_order_lexico _ _)).
  by iApply "post".
move: pt2 Ψ.
elim: pt1 => [o1|o1 t1 IH1|o1 t11 IH1 t12 IH2
             |ps1 /(PreTerm.foldr_Forall _ _) IHps1
                  ns1 /(PreTerm.foldr_Forall _ _) IHns1
             |l1 /(PreTerm.foldr_Forall_entries _ _) IHl1];
case => [o2|o2 t2|o2 t21 t22|ps2 ns2|l2] Ψ; rewrite ?repr_dhE;
iIntros "post"; rewrite pt_orderE /=; wp_rec; wp_pures; try by iApply "post".
- iApply twp_wand; first by wp_apply twp_leq_term_op0.
  by iIntros "% ->".
- wp_bind (eq_term_op1 _ _).
  iApply twp_wand; first by wp_apply twp_eq_term_op1.
  iIntros "% ->".
  case: (bool_decide_reflect (o1 = o2)) => e; wp_pures.
  + by iApply IH1.
  + iApply twp_wand; first by wp_apply twp_leq_term_op1.
    by iIntros "% ->".
- wp_bind (eq_term_op2 _ _).
  iApply twp_wand; first by wp_apply twp_eq_term_op2.
  iIntros "% ->".
  case: (bool_decide_reflect (o1 = o2)) => e1; wp_pures; last first.
    iApply twp_wand; first by wp_apply twp_leq_term_op2.
    by iIntros "% ->".
  wp_bind (eq_term _ _); iApply twp_eq_pre_term.
  case: (bool_decide_reflect (t11 = t21)) => e2; wp_pures.
  + by iApply IH2.
  + by iApply IH1.
- rewrite -!repr_list_val bool_decide_lexico_prod.
  wp_bind (eq_list _ _ _).
  iApply (twp_eq_list (A := PreTerm.pre_term)).
    by move=> x1 x2 Φ _; iIntros "post"; iApply twp_eq_pre_term.
  case: (bool_decide_reflect (ps1 = ps2)) => eP; wp_pures.
  + iApply (twp_leq_list _ _ _ _ _ feqP (IHl _ IHns1) with "[//]").
    by iIntros "_".
  + iApply (twp_leq_list _ _ _ _ _ feqP (IHl _ IHps1) with "[//]").
    by iIntros "_".
- iApply (twp_leq_list (A := entry) _ _ _ _ _ feqP' with "[//]").
    move=> e1 e2 e1_in Φ; iIntros "_ post".
    have := proj1 (Forall_forall _ _) IHl1 e1 e1_in.
    case: e1 e2 {e1_in} => [b1 [p1 n1]] [b2 [p2 n2]] /= [IHb [IHp IHn]].
    rewrite /repr_prod /= bool_decide_lexico_prod; wp_pures.
    wp_bind (eq_term _ _); iApply twp_eq_pre_term.
    case: (bool_decide_reflect (b1 = b2)) => eb; wp_pures; last first.
      iApply IHb; rewrite (bool_decide_ext _ _ (pt_order_lexico _ _)).
      by iApply "post".
    rewrite bool_decide_lexico_prod.
    wp_bind (eq_list _ _ _); iApply (twp_eq_list (A := PreTerm.pre_term)).
      by move=> x1 x2 Φ' _; iIntros "H"; iApply twp_eq_pre_term.
    case: (bool_decide_reflect (p1 = p2)) => ep; wp_pures.
    + iApply (twp_leq_list _ _ _ _ _ feqP (IHl _ IHn) with "[//]").
      iIntros "_"; by iApply "post".
    + iApply (twp_leq_list _ _ _ _ _ feqP (IHl _ IHp) with "[//]").
      iIntros "_"; by iApply "post".
  iIntros "_"; by iApply "post".
Qed.

Lemma twp_leq_pre_term_le pt1 pt2 E Ψ :
  Ψ #(bool_decide (MSet.le pt1 pt2)) ⊢
  WP (leq_term (repr pt1) (repr pt2)) @ E [{ Ψ }].
Proof.
rewrite (bool_decide_ext _ _ (iff_sym (pt_order_lexico pt1 pt2))).
exact: twp_leq_pre_term.
Qed.

(** ** Recognisers *)

Lemma twp_hl_is_exp pt E Ψ :
  Ψ #(PreTerm.is_exp pt) ⊢ WP hl_is_exp (repr pt) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam.
case: pt => [o|o t|o t1 t2|ps ns|l]; try by (wp_pures; iApply "HΨ").
rewrite val_dhE [@repr_list]unlock.
by case: l => [|[b [[|e [|??]] [|??]]] [|??]] /=; wp_pures; iApply "HΨ".
Qed.

Lemma twp_hl_is_mul pt E Ψ :
  Ψ #(PreTerm.is_mul pt) ⊢ WP hl_is_mul (repr pt) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam.
by case: pt => [o|o t|o t1 t2|ps ns|l] /=; wp_pures; iApply "HΨ".
Qed.

Lemma twp_hl_is_gmul pt E Ψ :
  Ψ #(PreTerm.is_gmul pt) ⊢ WP hl_is_gmul (repr pt) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam.
case: pt => [o|o t|o t1 t2|ps ns|l]; try by (wp_pures; iApply "HΨ").
wp_pures; wp_apply (twp_hl_is_exp (PreTerm.PTDH l)); wp_pures.
have -> : PreTerm.is_gmul (PreTerm.PTDH l) =
          negb (PreTerm.is_exp (PreTerm.PTDH l)).
  by case: l => [|[b [[|e [|??]] [|??]]] [|??]].
by iApply "HΨ".
Qed.

Lemma twp_hl_is_nonce pt E Ψ :
  Ψ #(PreTerm.is_nonce pt) ⊢ WP hl_is_nonce (repr pt) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam.
case: pt => [o|o t|o t1 t2|ps ns|l]; try by (wp_pures; iApply "HΨ").
by case: o => [n|a]; wp_pures; iApply "HΨ".
Qed.

(** ** Destructors *)

Lemma hl_oneE : hl_one = repr (PreTerm.PTMul [] []).
Proof. by rewrite /hl_one /= [@repr_list]unlock. Qed.

Lemma hl_goneE : hl_gone = repr (PreTerm.PTDH []).
Proof. by rewrite /hl_gone /= [@repr_list]unlock. Qed.

Lemma twp_hl_base pt E Ψ :
  Ψ (repr (PreTerm.base pt)) ⊢ WP hl_base (repr pt) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam.
wp_apply twp_hl_is_exp.
case: (PreTerm.is_expP pt) => [b e ->|_ -> _]; last by wp_pures; iApply "HΨ".
rewrite val_dhE [@repr_list]unlock /=; wp_pures.
by iApply "HΨ".
Qed.

Lemma twp_hl_expo pt E Ψ :
  Ψ (repr (PreTerm.expo pt)) ⊢ WP hl_expo (repr pt) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam.
wp_apply twp_hl_is_exp.
rewrite hl_oneE.
case: (PreTerm.is_expP pt) => [b e ->|_ _ ->]; last by wp_pures; iApply "HΨ".
rewrite val_dhE [@repr_list]unlock /=; wp_pures.
by iApply "HΨ".
Qed.

(* What [hl_factors] returns: the factors before normalization, which is the
   identity on well-formed pre-terms ([PreTerm.lists_factorsE]). *)
Definition raw_factors pt :=
  if pt is PreTerm.PTMul ps ns then (ps, ns) else ([pt], []).

#[local] Lemma reprS pt :
  repr ([pt], @nil PreTerm.pre_term) =
  (InjRV (repr pt, InjLV #()), InjLV #())%V.
Proof. by rewrite /= [@repr_list]unlock. Qed.

Lemma twp_hl_factors pt E Ψ :
  Ψ (repr (raw_factors pt)) ⊢ WP hl_factors (repr pt) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam.
wp_apply twp_hl_is_mul.
rewrite /raw_factors.
case: pt => [o|o t|o t1 t2|ps ns|l]; wp_pures.
all: try (rewrite /CONS; wp_pures; iEval (rewrite reprS) in "HΨ";
          by iApply "HΨ").
by rewrite -!repr_list_val; iApply "HΨ".
Qed.

Lemma twp_hl_mk_exp E (b e : PreTerm.pre_term) Ψ :
  Ψ (repr (PreTerm.mk_exp b e)) ⊢ WP hl_mk_exp (repr b) (repr e) @ E [{ Ψ }].
Proof.
have reprE :
    repr (PreTerm.PTDH [(b, ([e], []))]) =
    (#TDH_tag, InjRV ((repr b, (InjRV (repr e, InjLV #()), InjLV #())),
                      InjLV #()))%V.
  by rewrite repr_dhE /= [@repr_list]unlock.
iIntros "HΨ"; wp_lam; wp_pures; rewrite hl_oneE.
wp_apply twp_eq_pre_term.
rewrite /PreTerm.mk_exp.
case: (bool_decide (e = PreTerm.PTMul [] [])); wp_pures; first by iApply "HΨ".
rewrite /CONS; wp_pures; iEval (rewrite reprE) in "HΨ".
by iApply "HΨ".
Qed.

#[local] Lemma repr_sms_empty :
  repr (∅ : SMS.sms PreTerm.pre_term) = (NILV, NILV)%V.
Proof.
have lE : PreTerm.lists (∅ : SMS.sms PreTerm.pre_term) = ([], []) by [].
rewrite (_ : repr (∅ : SMS.sms _) = repr (PreTerm.lists ∅)) // lE.
by rewrite /= [@repr_list]unlock.
Qed.

(* [sms_map] on a pair of lists that need not be sorted or disjoint. *)
#[local] Lemma twp_sms_map_lists (f : PreTerm.pre_term → PreTerm.pre_term)
    (fv : val) (ps ns : list PreTerm.pre_term) E Ψ :
  (∀ y, [[{ True }]] fv (repr y) @ E [[{ RET repr (f y); True }]]) →
  Ψ (repr (SMS.map f (PreTerm.of_lists (ps, ns)))) ⊢
  WP sms_map eq_term leq_term fv (repr (ps, ns)%core) @ E [{ Ψ }].
Proof.
move=> fvP; iIntros "HΨ"; rewrite /repr_prod /=; wp_lam; wp_pures.
wp_apply (twp_map_list f fv ns) => //.
  by apply/Forall_forall => y _; apply: fvP.
iIntros "_"; wp_apply (twp_mset_of_list leq_term twp_leq_pre_term_le).
wp_pures.
wp_apply (twp_map_list f fv ps) => //.
  by apply/Forall_forall => y _; apply: fvP.
iIntros "_"; wp_apply (twp_mset_of_list leq_term twp_leq_pre_term_le).
wp_apply (twp_sms_to eq_term twp_eq_pre_term).
rewrite /PreTerm.of_lists SMS.map_make !MSet.map_of_list -!mapE.
by iApply "HΨ".
Qed.

Lemma twp_hl_dh_factors E (l : list entry) Ψ :
  Ψ (repr (PreTerm.dh_factors l)) ⊢ WP hl_dh_factors (repr l) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam; wp_pures.
rewrite -repr_sms_empty.
wp_apply (twp_foldr_list (λ (e : entry) s,
            SMS.map (PreTerm.mk_exp e.1) (PreTerm.of_lists e.2) ⊎ s)) => //.
- move=> [b [ps ns]] s Φ; iIntros "_ HΦ".
  rewrite (_ : repr (b, (ps, ns)) = (repr b, repr (ps, ns)%core)%V) //.
  wp_pures.
  wp_apply (twp_sms_map_lists (PreTerm.mk_exp b)).
    move=> y Φ'; iIntros "_ HΦ'"; wp_pures.
    by wp_apply twp_hl_mk_exp; iApply "HΦ'".
  wp_apply (twp_sms_disj_union eq_term leq_term twp_eq_pre_term
              twp_leq_pre_term_le).
  by iApply "HΦ".
- iIntros "_"; by iApply "HΨ".
Qed.

Lemma twp_hl_gfactors pt E Ψ :
  Ψ (repr (PreTerm.gfactors pt)) ⊢ WP hl_gfactors (repr pt) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam.
wp_apply twp_hl_is_gmul.
case Eg: (PreTerm.is_gmul pt); wp_pures.
  case: pt Eg => // l Eg.
  have -> : PreTerm.gfactors (PreTerm.PTDH l) = PreTerm.dh_factors l.
    by case: l Eg => [|[b [[|e [|??]] [|??]]] [|??]].
  rewrite val_dhE; wp_pures.
  wp_apply twp_hl_dh_factors; by iApply "HΨ".
rewrite PreTerm.gfactors_Ngmul ?Eg //.
rewrite (_ : repr {[+ pt +]} = repr (PreTerm.lists {[+ pt +]})) //.
rewrite PreTerm.lists_singleton.
by rewrite /CONS; wp_pures; iEval (rewrite reprS) in "HΨ"; iApply "HΨ".
Qed.

(* The same, with the two sides of the factors as lists. *)
Lemma twp_hl_gfactors_lists pt E Ψ :
  Ψ (repr (PreTerm.lists (PreTerm.gfactors pt))) ⊢
  WP hl_gfactors (repr pt) @ E [{ Ψ }].
Proof. exact: twp_hl_gfactors. Qed.

(** ** Smart constructors *)

Lemma twp_hl_mul_aux E (s : SMS.sms PreTerm.pre_term) Ψ :
  Ψ (repr (PreTerm.mul_aux s)) ⊢ WP hl_mul_aux (repr s) @ E [{ Ψ }].
Proof.
rewrite (_ : repr s = repr (PreTerm.lists s)) // /PreTerm.mul_aux.
case: (PreTerm.lists s) => [ps ns] /=; iIntros "HΨ"; wp_lam.
have mulE : (#TMul_tag, (repr_list ps, repr_list ns))%V =
            repr (PreTerm.PTMul ps ns).
  by rewrite /= -!repr_list_val.
rewrite /repr_prod /=.
case: ps mulE => [|t [|u ps]] mulE.
- rewrite ![repr_list []]repr_listE in mulE *; wp_pures.
  by rewrite mulE; iApply "HΨ".
- case: ns mulE => [|n ns] mulE.
    rewrite ?[repr_list (_ :: _)]repr_listE /= ?[repr_list []]repr_listE.
    by wp_pures; iApply "HΨ".
  rewrite {1}[repr_list [t]]repr_listE; wp_pures.
  rewrite {1}[repr_list []]repr_listE; wp_pures.
  rewrite {1}[repr_list (n :: ns)]repr_listE; wp_pures.
  by rewrite mulE; iApply "HΨ".
- rewrite {1}[repr_list (t :: u :: ps)]repr_listE; wp_pures.
  rewrite {1}[repr_list (u :: ps)]repr_listE; wp_pures.
  by rewrite mulE; iApply "HΨ".
Qed.

#[local] Lemma repr_dh_of (m : PreTerm.dhmap) :
  repr (PreTerm.dh_of m) =
  if PreTerm.entries m is [(b, ([e], []))] then repr (PreTerm.mk_exp b e)
  else (#TDH_tag, repr (PreTerm.entries m))%V.
Proof.
rewrite /PreTerm.dh_of.
by case: (PreTerm.entries m) => [|[b [[|e [|??]] [|??]]] [|??]] //;
  rewrite repr_dhE.
Qed.

Lemma twp_hl_dh_of E (m : PreTerm.dhmap) Ψ :
  Ψ (repr (PreTerm.dh_of m)) ⊢ WP hl_dh_of (repr m) @ E [{ Ψ }].
Proof.
have -> : repr m = repr (PreTerm.entries m).
  by rewrite repr_fmapE /PreTerm.entries repr_fmap_list // => -[k s].
rewrite repr_dh_of; iIntros "HΨ"; wp_lam.
case: (PreTerm.entries m) => [|[b [[|e [|??]] [|??]]] [|??]];
  rewrite [@repr_list]unlock /=; wp_pures; try by iApply "HΨ".
wp_apply twp_hl_mk_exp; by iApply "HΨ".
Qed.

Lemma twp_hl_curry_add E (sgnv : val)
    (sgn : PreTerm.pre_term → SMS.sms PreTerm.pre_term)
    pt (m : PreTerm.dhmap) Ψ :
  (∀ x Φ, Φ (repr (sgn x)) ⊢ WP sgnv (repr x) @ E [{ Φ }]) →
  Ψ (repr (SMS.curry_add (PreTerm.base pt) (sgn (PreTerm.expo pt)) m)) ⊢
  WP hl_curry_add sgnv (repr pt) (repr m) @ E [{ Ψ }].
Proof.
have dE : (NILV, NILV)%V = repr (∅ : SMS.sms PreTerm.pre_term).
  by rewrite repr_sms_empty.
have eqsP : ∀ (x y : SMS.sms PreTerm.pre_term) E Ψ,
    Ψ #(bool_decide (x = y)) ⊢
    WP (λ: "s1" "s2", sms_eq eq_term "s1" "s2")%V (repr x) (repr y) @ E
      [{ Ψ }].
  move=> x y E' Ψ'; iIntros "H"; wp_pures.
  by wp_apply (twp_sms_eq eq_term twp_eq_pre_term).
move=> sgnP; iIntros "HΨ"; wp_lam; wp_pures.
wp_apply twp_hl_base; wp_pures; rewrite dE.
wp_apply (twp_fmap_lookup eq_term twp_eq_pre_term); wp_pures.
wp_apply twp_hl_expo; wp_apply sgnP.
wp_apply (twp_sms_disj_union eq_term leq_term twp_eq_pre_term
            twp_leq_pre_term_le); wp_pures; rewrite dE.
wp_apply (twp_fmap_insert eq_term leq_term twp_eq_pre_term
            twp_leq_pre_term_le _ _ eqsP).
by iApply "HΨ".
Qed.

Lemma twp_hl_gmul_aux E (s : SMS.sms PreTerm.pre_term) Ψ :
  Ψ (repr (PreTerm.gmul_aux s)) ⊢ WP hl_gmul_aux (repr s) @ E [{ Ψ }].
Proof.
have posP : ∀ x Φ,
    Φ (repr ({[+ x +]} : SMS.sms PreTerm.pre_term)) ⊢
    WP (λ: "x", ("x" :: NILV, NILV))%V (repr x) @ E [{ Φ }].
  move=> x Φ; iIntros "H"; rewrite /CONS; wp_pures.
  rewrite (_ : repr {[+ x +]} = repr (PreTerm.lists {[+ x +]})) //.
  rewrite PreTerm.lists_singleton reprS; by iApply "H".
have negP : ∀ x Φ,
    Φ (repr (SMS.inv {[+ x +]} : SMS.sms PreTerm.pre_term)) ⊢
    WP (λ: "x", (NILV, "x" :: NILV))%V (repr x) @ E [{ Φ }].
  move=> x Φ; iIntros "H"; rewrite /CONS; wp_pures.
  rewrite (_ : repr (SMS.inv {[+ x +]}) =
               (repr (PreTerm.lists {[+ x +]}).2,
                repr (PreTerm.lists {[+ x +]}).1)%V) //.
  rewrite PreTerm.lists_singleton /= [@repr_list]unlock; by iApply "H".
rewrite PreTerm.gmul_auxE (_ : repr s = repr (PreTerm.lists s)) //.
rewrite /PreTerm.lists /repr_prod /=.
iIntros "HΨ"; wp_lam; wp_pures.
rewrite (_ : fmap_empty = repr (∅ : PreTerm.dhmap));
  last by rewrite repr_fmap_empty.
wp_apply (twp_foldr_list
            (λ t m, SMS.curry_add (PreTerm.base t)
                      (SMS.inv {[+ PreTerm.expo t +]}) m)) => //.
  move=> t m Φ; iIntros "_ HΦ"; wp_pures.
  wp_apply (twp_hl_curry_add _ _ (λ x, SMS.inv {[+ x +]}) _ _ _ negP).
  by iApply "HΦ".
iIntros "_"; wp_pures.
wp_apply (twp_foldr_list
            (λ t m, SMS.curry_add (PreTerm.base t) {[+ PreTerm.expo t +]} m))
  => //.
  move=> t m Φ; iIntros "_ HΦ"; wp_pures.
  wp_apply (twp_hl_curry_add _ _ (λ x, {[+ x +]}) _ _ _ posP).
  by iApply "HΦ".
iIntros "_"; wp_apply twp_hl_dh_of; by iApply "HΨ".
Qed.

(* What [hl_flat] computes: the elements of [A] multiplied out through [f],
   with the sides of the image of a negative element swapped. *)
Definition flat {T U} (f : T → list U * list U) (A : list T * list T) :=
  (mbind (λ t, (f t).1) A.1 ++ mbind (λ t, (f t).2) A.2,
   mbind (λ t, (f t).2) A.1 ++ mbind (λ t, (f t).1) A.2).

Section Flat.

Context (f : PreTerm.pre_term → list PreTerm.pre_term * list PreTerm.pre_term).
Context (fv : val).
Hypothesis fvP : ∀ pt E Ψ, Ψ (repr (f pt)) ⊢ WP fv (repr pt) @ E [{ Ψ }].

Lemma twp_hl_bind_fst E (ts : list PreTerm.pre_term) Ψ :
  Ψ (repr (mbind (λ t, (f t).1) ts)) ⊢
  WP hl_bind_fst fv (repr ts) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam; wp_pures; wp_apply twp_nil.
wp_apply (twp_foldr_list (λ (t : PreTerm.pre_term) acc, (f t).1 ++ acc)) => //.
  iIntros "%b %a %Φ _ HΦ"; wp_pures.
  wp_apply fvP; wp_pures; wp_apply twp_append_lists.
  by iApply "HΦ".
iIntros "_"; by iApply "HΨ".
Qed.

Lemma twp_hl_bind_snd E (ts : list PreTerm.pre_term) Ψ :
  Ψ (repr (mbind (λ t, (f t).2) ts)) ⊢
  WP hl_bind_snd fv (repr ts) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam; wp_pures; wp_apply twp_nil.
wp_apply (twp_foldr_list (λ (t : PreTerm.pre_term) acc, (f t).2 ++ acc)) => //.
  iIntros "%b %a %Φ _ HΦ"; wp_pures.
  wp_apply fvP; wp_pures; wp_apply twp_append_lists.
  by iApply "HΦ".
iIntros "_"; by iApply "HΨ".
Qed.

Lemma twp_hl_flat E (A : list PreTerm.pre_term * list PreTerm.pre_term) Ψ :
  Ψ (repr (flat f A)) ⊢ WP hl_flat fv (repr A) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; case: A => [ps ns]; rewrite /repr_prod /=; wp_lam; wp_pures.
wp_apply (twp_hl_bind_fst _ ns); wp_pures; wp_apply (twp_hl_bind_snd _ ps).
wp_apply twp_append_lists; wp_pures.
wp_apply (twp_hl_bind_snd _ ns); wp_pures; wp_apply (twp_hl_bind_fst _ ps).
wp_apply twp_append_lists.
by wp_pures; iApply "HΨ".
Qed.

End Flat.

#[local] Lemma flat_ext {T U} (f g : T → list U * list U) A :
  (∀ x, x ∈ A.1 ++ A.2 → f x = g x) → flat f A = flat g A.
Proof.
case: A => [X Y] /= /Forall_forall /Forall_app [eX eY].
have h (l : list T) (p : list U * list U → list U) :
    Forall (λ x, f x = g x) l → l ≫= (λ x, p (f x)) = l ≫= (λ x, p (g x)).
  move=> el; apply: Forall_bind_ext.
  by apply: (Forall_impl _ _ _ el) => x ->.
by rewrite /flat /= (h X fst) // (h X snd) // (h Y fst) // (h Y snd).
Qed.

Lemma bind_flat f g A :
  (∀ x, x ∈ A.1 ++ A.2 → PreTerm.lists (f x) = g x) →
  SMS.bind f (SMS.make (MSet.of_list A.1) (MSet.of_list A.2)) =
  SMS.make (MSet.of_list (flat g A).1) (MSet.of_list (flat g A).2).
Proof.
move=> /flat_ext <-.
by rewrite SMS.bind_make !MSet.bind_of_list -!MSet.of_list_app.
Qed.

Lemma twp_hl_normalize_factors E A Ψ :
  (∀ x, x ∈ A.1 ++ A.2 → PreTerm.wf x) →
  Ψ (repr (SMS.bind PreTerm.factors
            (SMS.make (MSet.of_list A.1) (MSet.of_list A.2))))
  ⊢ WP hl_normalize_factors (repr A) @ E [{ Ψ }].
Proof.
move=> wfA.
have e x :
    x ∈ A.1 ++ A.2 → PreTerm.lists (PreTerm.factors x) = raw_factors x.
  by move=> /wfA; exact: PreTerm.lists_factorsE.
rewrite (bind_flat _ _ _ e); iIntros "HΨ"; wp_lam.
wp_apply (twp_hl_flat raw_factors _ twp_hl_factors); wp_pures.
wp_apply (twp_mset_of_list leq_term twp_leq_pre_term_le); wp_pures.
wp_apply (twp_mset_of_list leq_term twp_leq_pre_term_le).
wp_apply (twp_sms_to eq_term twp_eq_pre_term).
by iApply "HΨ".
Qed.

Lemma twp_hl_normalize_gfactors E A Ψ :
  Ψ (repr (SMS.bind PreTerm.gfactors
            (SMS.make (MSet.of_list A.1) (MSet.of_list A.2))))
  ⊢ WP hl_normalize_gfactors (repr A) @ E [{ Ψ }].
Proof.
rewrite (bind_flat _ (λ x, PreTerm.lists (PreTerm.gfactors x))) //.
iIntros "HΨ"; wp_lam.
wp_apply (twp_hl_flat (λ x, PreTerm.lists (PreTerm.gfactors x)) _
            twp_hl_gfactors); wp_pures.
wp_apply (twp_mset_of_list leq_term twp_leq_pre_term_le); wp_pures.
wp_apply (twp_mset_of_list leq_term twp_leq_pre_term_le).
wp_apply (twp_sms_to eq_term twp_eq_pre_term).
by iApply "HΨ".
Qed.

Lemma twp_hl_mul_pair E A Ψ :
  (∀ x, x ∈ A.1 ++ A.2 → PreTerm.wf x) →
  Ψ (repr (PreTerm.mul (SMS.make (MSet.of_list A.1) (MSet.of_list A.2)))) ⊢
  WP hl_mul_pair (repr A) @ E [{ Ψ }].
Proof.
move=> wfA; iIntros "HΨ"; wp_lam; rewrite PreTerm.mulE.
wp_apply (twp_hl_normalize_factors _ _ _ wfA).
wp_apply twp_hl_mul_aux.
by iApply "HΨ".
Qed.

Lemma twp_hl_gmul_pair E A Ψ :
  Ψ (repr (PreTerm.gmul (SMS.make (MSet.of_list A.1) (MSet.of_list A.2)))) ⊢
  WP hl_gmul_pair (repr A) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam.
wp_apply twp_hl_normalize_gfactors.
wp_apply twp_hl_gmul_aux.
by iApply "HΨ".
Qed.

#[local] Lemma make_pair x y :
  SMS.make (MSet.of_list [x; y]) (MSet.of_list []) = {[+ x; y +]}.
Proof.
rewrite !MSet.of_list_cons MSet.of_list_nil (right_id ∅ (⊎)).
by rewrite SMS.make_singleton_l -SMS.singleton_make.
Qed.

#[local] Lemma make_inv x :
  SMS.make (MSet.of_list []) (MSet.of_list [x]) = SMS.inv {[+ x +]}.
Proof.
rewrite MSet.of_list_cons MSet.of_list_nil (right_id ∅ (⊎)).
by rewrite SMS.singleton_make SMS.inv_make.
Qed.

Lemma twp_hl_mul E pt1 pt2 Ψ :
  PreTerm.wf pt1 → PreTerm.wf pt2 →
  Ψ (repr (PreTerm.mul {[+ pt1; pt2 +]})) ⊢
  WP hl_mul (repr pt1) (repr pt2) @ E [{ Ψ }].
Proof.
move=> wf1 wf2; rewrite -make_pair.
iIntros "HΨ"; wp_lam; wp_pures; rewrite /CONS; wp_pures.
rewrite (_ : (InjRV (val_of_pre_term pt1,
                     InjRV (val_of_pre_term pt2, [])), [])%V =
             repr ([pt1; pt2], @nil PreTerm.pre_term)); last first.
  by rewrite /= [@repr_list]unlock.
wp_apply twp_hl_mul_pair; last by iApply "HΨ".
by move=> x; rewrite /= elem_of_cons list_elem_of_singleton => -[->|->].
Qed.

Lemma twp_hl_gmul E pt1 pt2 Ψ :
  PreTerm.wf pt1 → PreTerm.wf pt2 →
  Ψ (repr (PreTerm.gmul {[+ pt1; pt2 +]})) ⊢
  WP hl_gmul (repr pt1) (repr pt2) @ E [{ Ψ }].
Proof.
move=> wf1 wf2; rewrite -make_pair.
iIntros "HΨ"; wp_lam; wp_pures; rewrite /CONS; wp_pures.
rewrite (_ : (InjRV (val_of_pre_term pt1,
                     InjRV (val_of_pre_term pt2, [])), [])%V =
             repr ([pt1; pt2], @nil PreTerm.pre_term)); last first.
  by rewrite /= [@repr_list]unlock.
wp_apply twp_hl_gmul_pair; by iApply "HΨ".
Qed.

Lemma twp_hl_inv E pt Ψ :
  PreTerm.wf pt →
  Ψ (repr (PreTerm.mul (SMS.inv {[+ pt +]}))) ⊢
  WP hl_inv (repr pt) @ E [{ Ψ }].
Proof.
move=> wf_pt; rewrite -make_inv.
iIntros "HΨ"; wp_lam; wp_pures; rewrite /CONS; wp_pures.
rewrite (_ : ([], InjRV (val_of_pre_term pt, []))%V =
             repr (@nil PreTerm.pre_term, [pt])); last first.
  by rewrite /= [@repr_list]unlock.
wp_apply twp_hl_mul_pair; last by iApply "HΨ".
by move=> x; rewrite /= list_elem_of_singleton => ->.
Qed.

Lemma twp_hl_ginv E pt Ψ :
  PreTerm.wf pt →
  Ψ (repr (PreTerm.gmul (SMS.inv {[+ pt +]}))) ⊢
  WP hl_ginv (repr pt) @ E [{ Ψ }].
Proof.
move=> wf_pt; rewrite -make_inv.
iIntros "HΨ"; wp_lam; wp_pures; rewrite /CONS; wp_pures.
rewrite (_ : ([], InjRV (val_of_pre_term pt, []))%V =
             repr (@nil PreTerm.pre_term, [pt])); last first.
  by rewrite /= [@repr_list]unlock.
wp_apply twp_hl_gmul_pair; by iApply "HΨ".
Qed.

Lemma twp_hl_exp_aux E (b e : PreTerm.pre_term) Ψ :
  PreTerm.wf b → PreTerm.wf e →
  Ψ (repr (PreTerm.exp_aux b e)) ⊢ WP hl_exp_aux (repr b) (repr e) @ E [{ Ψ }].
Proof.
move=> wf_b wf_e; rewrite /PreTerm.exp_aux -make_pair.
iIntros "HΨ"; wp_lam; wp_pures; rewrite /CONS; wp_pures.
wp_apply twp_hl_expo; wp_pures.
rewrite (_ : (InjRV (repr (PreTerm.expo b),
                     InjRV (val_of_pre_term e, [])), [])%V =
             repr ([PreTerm.expo b; e], @nil PreTerm.pre_term)); last first.
  by rewrite /= [@repr_list]unlock.
wp_apply twp_hl_mul_pair.
  move=> x; rewrite /= elem_of_cons.
  by rewrite list_elem_of_singleton => -[->|->] //; exact: PreTerm.wf_expo.
wp_apply twp_hl_base.
wp_apply twp_hl_mk_exp.
by iApply "HΨ".
Qed.

#[local] Lemma map_lists (f : PreTerm.pre_term → PreTerm.pre_term) s :
  SMS.map f s =
  SMS.make (MSet.of_list (f <$> (PreTerm.lists s).1))
           (MSet.of_list (f <$> (PreTerm.lists s).2)).
Proof.
rewrite SMS.map_pos_neg /PreTerm.lists; cbn [fst snd].
by rewrite -!MSet.map_of_list !MSet.of_list_elements.
Qed.

Lemma twp_hl_exp E (b e : PreTerm.pre_term) Ψ :
  PreTerm.wf b → PreTerm.wf e →
  Ψ (repr (PreTerm.exp b e)) ⊢ WP hl_exp (repr b) (repr e) @ E [{ Ψ }].
Proof.
move=> wf_b wf_e.
have wfg := PreTerm.wf_wf_gfactors _ wf_b.
have expS : ∀ pt' : PreTerm.pre_term, pt' ∈ PreTerm.gfactors b →
    [[{ True }]] (λ: "t", hl_exp_aux "t" (repr e))%V (repr pt') @ E
    [[{ RET repr (PreTerm.exp_aux pt' e); True }]].
  iIntros "%pt' %pt'_b %Φ _ HΦ"; wp_pures.
  wp_apply twp_hl_exp_aux; last by iApply "HΦ".
  - exact: PreTerm.wf_gfactors_wf wfg pt'_b.
  - exact: wf_e.
iIntros "HΨ"; wp_lam; wp_pures.
wp_apply twp_hl_gfactors_lists.
rewrite /PreTerm.exp map_lists.
have elemE x : x ∈ (PreTerm.lists (PreTerm.gfactors b)).1 ∨
               x ∈ (PreTerm.lists (PreTerm.gfactors b)).2 →
               x ∈ PreTerm.gfactors b.
  by rewrite -SMS.elem_of_elements PreTerm.elements_lists elem_of_app.
case: (PreTerm.lists (PreTerm.gfactors b)) elemE => [ps ns] /= elemE.
rewrite /repr_prod /=; wp_pures.
wp_apply (twp_map_list (fun t => PreTerm.exp_aux t e) _ ns) => //.
  by apply/Forall_forall => x x_ns; apply: expS; apply: elemE; right.
iIntros "_"; wp_pures.
wp_apply (twp_map_list (fun t => PreTerm.exp_aux t e) _ ps) => //.
  by apply/Forall_forall => x x_ps; apply: expS; apply: elemE; left.
iIntros "_"; wp_pures; rewrite !mapE.
rewrite (_ : (repr ((λ t, PreTerm.exp_aux t e) <$> ps),
              repr ((λ t, PreTerm.exp_aux t e) <$> ns))%V =
             repr ((λ t, PreTerm.exp_aux t e) <$> ps,
                   (λ t, PreTerm.exp_aux t e) <$> ns)) //.
wp_apply twp_hl_gmul_pair; by iApply "HΨ".
Qed.

End Proofs.
