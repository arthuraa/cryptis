(* HeapLang implementations of the pre-term operations of
   [core/pre_term/normalize.v], together with specs saying that each program
   computes the corresponding pure function.

   Every pure function of [normalize.v] has a counterpart here:

     is_exp / is_mul / is_gmul / is_nonce  ->  hl_is_exp / hl_is_mul /
                                               hl_is_gmul / hl_is_nonce
     base / expo                           ->  hl_base / hl_expo
     factors / gfactors                    ->  hl_factors / hl_gfactors
     mul_aux / gmul_aux                    ->  hl_mul_aux / hl_gmul_aux
     SMS.Internal.flat                     ->  hl_flat
     SMS.bind factors / SMS.bind gfactors  ->  hl_normalize_factors /
                                               hl_normalize_gfactors
     mul / gmul                            ->  hl_mul_pair / hl_gmul_pair
     mk_exp / exp_aux / exp                ->  hl_mk_exp / hl_exp_aux / hl_exp

   Pairs of lists are represented as HeapLang pairs ([repr_prod]).
   [hl_mul]/[hl_inv] (and [hl_gmul]/[hl_ginv]) are [hl_mul_pair] at
   [([t1; t2], [])] and [([], [t])].

   [normalize] itself is not implemented: the HeapLang layer only ever builds
   pre-terms with the smart constructors, so it never needs to renormalise.

   The product machinery is not reimplemented here.  [SMS.bind factors] is
   [SMS.Internal.to SMS.Internal.le] applied to the flattened factor lists
   ([car_bind_factors]), so [hl_normalize_factors] is just [sms_to] from
   [primitives/sms.v] instantiated at the pre-term order, and its spec is
   [twp_sms_to].

   These proofs take much longer to check than the rest of the development.
   Since they don't have many dependencies, they are left in their own file to
   avoid slowing down the compilation process. *)

From mathcomp Require Import ssreflect.
From stdpp Require Import list sorting lexico.
From iris.heap_lang Require Import notation proofmode.
From cryptis.lib Require Import repr list list_sort sms.
From cryptis.core Require Import pre_term.
From cryptis.primitives Require Import sms.

Unset Printing Implicit Defensive.

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

Definition eq_term_opN : val := λ: "x" "y",
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
    else if: "tag" = #TOpN_tag then
      eq_term_opN (Fst (Fst (Snd "x"))) (Fst (Fst (Snd "y"))) &&
      eq_list "eq" (Snd (Fst (Snd "x"))) (Snd (Fst (Snd "y"))) &&
      eq_list "eq" (Snd (Snd "x")) (Snd (Snd "y"))
    else #false
  else #false)%V.

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

Definition leq_term_opN : val := λ: "x" "y",
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
    else if: "tag" = #TOpN_tag then
      let: "o1" := Fst (Fst "a1") in
      let: "o2" := Fst (Fst "a2") in
      if: eq_term_opN "o1" "o2" then
        (if: eq_list eq_term (Snd (Fst "a1")) (Snd (Fst "a2"))
         then leq_list eq_term "loop" (Snd "a1") (Snd "a2")
         else leq_list eq_term "loop" (Snd (Fst "a1")) (Snd (Fst "a2")))
      else leq_term_opN "o1" "o2"
    else #false
  else #false)%V.

(** ** Recognisers *)

Definition hl_is_exp : val := λ: "pt",
  if: Fst "pt" = #TOp2_tag then Fst (Fst (Snd "pt")) = #TExp_tag else #false.

Definition hl_is_mul : val := λ: "pt",
  if: Fst "pt" = #TOpN_tag then Fst (Fst (Snd "pt")) = #TMul_tag else #false.

Definition hl_is_gmul : val := λ: "pt",
  if: Fst "pt" = #TOpN_tag then Fst (Fst (Snd "pt")) = #TGMul_tag else #false.

Definition hl_is_nonce : val := λ: "pt",
  if: Fst "pt" = #TOp0_tag then Fst (Snd "pt") = #TNonce_tag else #false.

(** ** Destructors *)

(* [repr (PreTerm.PTMul [] [])], i.e. the unit of the product. *)
Definition hl_one : val := (#TOpN_tag, (#TMul_tag, NILV, NILV))%V.

Definition hl_gone : val := (#TOpN_tag, (#TGMul_tag, NILV, NILV))%V.

Definition hl_base : val := λ: "pt",
  if: hl_is_exp "pt" then Snd (Fst (Snd "pt")) else "pt".

Definition hl_expo : val := λ: "pt",
  if: hl_is_exp "pt" then Snd (Snd "pt") else hl_one.

Definition hl_factors : val := λ: "pt",
  if: hl_is_mul "pt" then (Snd (Fst (Snd "pt")), Snd (Snd "pt"))
  else ("pt" :: NILV, NILV).

Definition hl_gfactors : val := λ: "pt",
  if: hl_is_gmul "pt" then (Snd (Fst (Snd "pt")), Snd (Snd "pt"))
  else ("pt" :: NILV, NILV).

(** ** Smart constructors *)

Definition hl_mul_aux : val := λ: "A",
  match: Fst "A" with
    NONE => (#TOpN_tag, (#TMul_tag, Fst "A", Snd "A"))
  | SOME "x" =>
      match: Snd "x" with
        NONE =>
          match: Snd "A" with
            NONE => Fst "x"
          | SOME <> => (#TOpN_tag, (#TMul_tag, Fst "A", Snd "A"))
          end
      | SOME <> => (#TOpN_tag, (#TMul_tag, Fst "A", Snd "A"))
      end
  end.

Definition hl_gmul_aux : val := λ: "A",
  match: Fst "A" with
    NONE => (#TOpN_tag, (#TGMul_tag, Fst "A", Snd "A"))
  | SOME "x" =>
      match: Snd "x" with
        NONE =>
          match: Snd "A" with
            NONE => Fst "x"
          | SOME <> => (#TOpN_tag, (#TGMul_tag, Fst "A", Snd "A"))
          end
      | SOME <> => (#TOpN_tag, (#TGMul_tag, Fst "A", Snd "A"))
      end
  end.

(* [mbind (λ t, (f t).1)] and [mbind (λ t, (f t).2)]. *)
Definition hl_bind_fst : val := λ: "f" "l",
  foldr_list (λ: "t" "acc", append_lists (Fst ("f" "t")) "acc") [] "l".

Definition hl_bind_snd : val := λ: "f" "l",
  foldr_list (λ: "t" "acc", append_lists (Snd ("f" "t")) "acc") [] "l".

Definition hl_flat : val := λ: "f" "A",
  (append_lists (hl_bind_fst "f" (Fst "A")) (hl_bind_snd "f" (Snd "A")),
   append_lists (hl_bind_snd "f" (Fst "A")) (hl_bind_fst "f" (Snd "A"))).

(* [SMS.bind PreTerm.factors] is [SMS.Internal.to SMS.Internal.le] of the
   flattened factors, so this is [sms_to] at the pre-term instance. *)
Definition hl_normalize_factors : val := λ: "A",
  sms_to leq_term eq_term (hl_flat hl_factors "A").

Definition hl_normalize_gfactors : val := λ: "A",
  sms_to leq_term eq_term (hl_flat hl_gfactors "A").

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

Definition hl_mk_exp : val := λ: "b" "e",
  if: eq_term "e" hl_one then "b" else (#TOp2_tag, (#TExp_tag, "b", "e")).

Definition hl_exp_aux : val := λ: "b" "e",
  hl_mk_exp (hl_base "b") (hl_mul_pair (hl_expo "b" :: "e" :: NILV, NILV)).

(* [exp] spreads [exp_aux] over the group factors. *)
Definition hl_exp : val := λ: "b" "e",
  let: "A" := hl_gfactors "b" in
  let: "f" := (λ: "t", hl_exp_aux "t" "e") in
  hl_gmul_pair (map_list "f" (Fst "A"), map_list "f" (Snd "A")).

Definition texp : val := λ: "base" "exp", hl_exp "base" "exp".

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

Lemma twp_eq_term_opN E (o1 o2 : term_opN) :
  ⊢ WP (eq_term_opN (repr o1) (repr o2)) @ E
    [{ v, ⌜v = #(bool_decide (o1 = o2))⌝}].
Proof. case: o1 o2 => [|] [|] /=; wp_lam; wp_pures => //. Qed.

#[local] Definition eq_term_spec E pt1 : Prop :=
  ∀ pt2, ⊢ WP (eq_term (repr pt1) (repr pt2)) @ E
              [{ v, ⌜v = #(bool_decide (pt1 = pt2))⌝ }].

Lemma twp_eq_pre_term_aux E pt1 pt2 :
  ⊢ WP (eq_term (repr pt1) (repr pt2)) @ E
       [{ v, ⌜v = #(bool_decide (pt1 = pt2))⌝ }].
Proof.
have IHl (ts : list PreTerm.pre_term) :
    foldr (λ t R, eq_term_spec E t * R)%type unit ts →
    ∀ x1 x2 Ψ, x1 ∈ ts →
      Ψ #(bool_decide (x1 = x2)) -∗
      WP eq_term (repr x1) (repr x2) @ E [{ Ψ }].
  elim: ts => [_ x1 x2 Ψ /elem_of_nil []|t ts IH [IHt /IH IHts] x1 x2 Ψ].
  rewrite elem_of_cons; case=> [->|x1_in]; iIntros "post"; last first.
    by iApply IHts.
  iApply twp_wand; first iApply IHt; by iIntros (?) "->".
move: pt2.
elim: pt1 => [o1|o1 t1 IH1|o1 t11 IH1 t12 IH2|oN1 ps1 IHps1 ns1 IHns1];
case=> [o2|o2 t2|o2 t21 t22|oN2 ps2 ns2]; wp_rec; wp_pures=> //.
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
- wp_bind (eq_term_opN _ _).
  iApply twp_wand; first by wp_apply (twp_eq_term_opN _ oN1 oN2).
  iIntros (?) "->".
  case: (bool_decide_reflect (oN1 = oN2)) => eN; wp_pures; last first.
    by iPureIntro; congr (# (LitBool _)); rewrite bool_decide_false; congruence.
  rewrite -!repr_list_val.
  wp_bind (eq_list _ _ _).
  iApply (twp_eq_list (A := PreTerm.pre_term) _ _ _ _ _ (IHl _ IHps1)).
  case: (bool_decide_reflect (ps1 = ps2)) => eP; wp_pures; last first.
    by iPureIntro; congr (# (LitBool _)); rewrite bool_decide_false; congruence.
  iApply (twp_eq_list (A := PreTerm.pre_term) _ _ _ _ _ (IHl _ IHns1)).
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

Lemma twp_leq_term_opN E (o1 o2 : term_opN) :
  ⊢ WP (leq_term_opN (repr o1) (repr o2)) @ E [{ v, ⌜v = #(opN_le o1 o2)⌝}].
Proof. by case: o1 o2 => [|] [|] /=; wp_lam; wp_pures. Qed.

Lemma bool_decide_lexico_pair (ps1 ns1 ps2 ns2 : list PreTerm.pre_term) :
  bool_decide ((ps1, ns1) = (ps2, ns2) ∨ lexico (ps1, ns1) (ps2, ns2)) =
  if bool_decide (ps1 = ps2) then bool_decide (ns1 = ns2 ∨ lexico ns1 ns2)
  else bool_decide (ps1 = ps2 ∨ lexico ps1 ps2).
Proof.
have E : lexico (ps1, ns1) (ps2, ns2) ↔
         lexico ps1 ps2 ∨ ps1 = ps2 ∧ lexico ns1 ns2 by [].
move: E; case: (bool_decide_reflect (ps1 = ps2)) => [<-|ne] E;
  apply: bool_decide_ext; rewrite E; split.
- case=> [[->]|[l|[_ l]]]; [by left|by case: (irreflexivity _ _ l)|by right].
- by case=> [->|l]; [left|right; right].
- by case=> [[e _]|[l|[e _]]]; [|right|].
- by case=> [e|l]; [|right; left].
Qed.

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
have IHl (ts : list PreTerm.pre_term) :
    foldr (λ t R, leq_term_spec E t * R)%type unit ts →
    ∀ x1 x2 : PreTerm.pre_term, x1 ∈ ts →
    [[{ True }]] leq_term (repr x1) (repr x2) @ E
    [[{ RET #(bool_decide (x1 = x2 ∨ lexico x1 x2)); True }]].
  elim: ts => [_ x1 x2 /elem_of_nil []|y ts IH [IHy /IH IHts] x1 x2].
  rewrite elem_of_cons => - [->|x1_in] Φ; iIntros "_ post".
  + iApply IHy; rewrite (bool_decide_ext _ _ (pt_order_lexico _ _)).
    by iApply "post".
  + by iApply (IHts x1 x2 x1_in with "[//] post").
move: pt2 Ψ.
elim: pt1 => [o1|o1 t1 IH1|o1 t11 IH1 t12 IH2|oN1 ps1 IHps1 ns1 IHns1];
case => [o2|o2 t2|o2 t21 t22|oN2 ps2 ns2] Ψ;
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
wp_bind (eq_term_opN _ _).
iApply twp_wand; first by wp_apply (twp_eq_term_opN _ oN1 oN2).
iIntros "% ->".
case: (bool_decide_reflect (oN1 = oN2)) => eN; wp_pures; last first.
  iApply twp_wand; first by wp_apply twp_leq_term_opN.
  by iIntros "% ->".
rewrite -!repr_list_val bool_decide_lexico_pair.
wp_bind (eq_list _ _ _).
iApply (twp_eq_list (A := PreTerm.pre_term)).
  by move=> x1 x2 Φ _; iIntros "post"; iApply twp_eq_pre_term.
case: (bool_decide_reflect (ps1 = ps2)) => eP; wp_pures.
- iApply (twp_leq_list _ _ _ _ _ feqP (IHl _ IHns1) with "[//]").
  by iIntros "_".
- iApply (twp_leq_list _ _ _ _ _ feqP (IHl _ IHps1) with "[//]").
  by iIntros "_".
Qed.

(** ** Recognisers *)

Lemma twp_hl_is_exp pt E Ψ :
  Ψ #(PreTerm.is_exp pt) ⊢ WP hl_is_exp (repr pt) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam.
case: pt => [o|o t|o t1 t2|[|] ps ns]; try by (wp_pures; iApply "HΨ").
all: by case: o; wp_pures; iApply "HΨ".
Qed.

Lemma twp_hl_is_mul pt E Ψ :
  Ψ #(PreTerm.is_mul pt) ⊢ WP hl_is_mul (repr pt) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam.
by case: pt => [o|o t|o t1 t2|[|] ps ns] /=; wp_pures; iApply "HΨ".
Qed.

Lemma twp_hl_is_gmul pt E Ψ :
  Ψ #(PreTerm.is_gmul pt) ⊢ WP hl_is_gmul (repr pt) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam.
by case: pt => [o|o t|o t1 t2|[|] ps ns] /=; wp_pures; iApply "HΨ".
Qed.

Lemma twp_hl_is_nonce pt E Ψ :
  Ψ #(PreTerm.is_nonce pt) ⊢ WP hl_is_nonce (repr pt) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam.
case: pt => [o|o t|o t1 t2|[|] ps ns]; try by (wp_pures; iApply "HΨ").
all: by case: o => [n|a]; wp_pures; iApply "HΨ".
Qed.

(** ** Destructors *)

Lemma hl_oneE : hl_one = repr (PreTerm.PTMul [] []).
Proof. by rewrite /hl_one /= [@repr_list]unlock. Qed.

Lemma hl_goneE : hl_gone = repr (PreTerm.PTGMul [] []).
Proof. by rewrite /hl_gone /= [@repr_list]unlock. Qed.

Lemma twp_hl_base pt E Ψ :
  Ψ (repr (PreTerm.base pt)) ⊢ WP hl_base (repr pt) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam.
wp_apply twp_hl_is_exp.
case: pt => [o|o t|o t1 t2|[|] ps ns]; try by (wp_pures; iApply "HΨ").
all: by case: o; wp_pures; iApply "HΨ".
Qed.

Lemma twp_hl_expo pt E Ψ :
  Ψ (repr (PreTerm.expo pt)) ⊢ WP hl_expo (repr pt) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam.
wp_apply twp_hl_is_exp.
rewrite /PreTerm.expo hl_oneE.
case: pt => [o|o t|o t1 t2|[|] ps ns]; try by (wp_pures; iApply "HΨ").
all: by case: o; wp_pures; iApply "HΨ".
Qed.

(* What [hl_factors] and [hl_gfactors] return: the factors before
   normalization, which is the identity on well-formed pre-terms
   ([PreTerm.car_factorsE]). *)
Definition raw_factors pt :=
  if pt is PreTerm.PTMul ps ns then (ps, ns) else ([pt], []).

Definition raw_gfactors pt :=
  if pt is PreTerm.PTGMul ps ns then (ps, ns) else ([pt], []).

Lemma twp_hl_factors pt E Ψ :
  Ψ (repr (raw_factors pt)) ⊢ WP hl_factors (repr pt) @ E [{ Ψ }].
Proof.
have reprS : ∀ pt' : PreTerm.pre_term,
    repr ([pt'], @nil PreTerm.pre_term) =
    (InjRV (repr pt', InjLV #()), InjLV #())%V.
  by move=> pt'; rewrite /= [@repr_list]unlock.
iIntros "HΨ"; wp_lam.
wp_apply twp_hl_is_mul.
rewrite /raw_factors.
case: pt => [o|o t|o t1 t2|[|] ps ns]; wp_pures.
all: try (rewrite /CONS; wp_pures; iEval (rewrite reprS) in "HΨ";
          by iApply "HΨ").
by rewrite -!repr_list_val; iApply "HΨ".
Qed.

Lemma twp_hl_gfactors pt E Ψ :
  Ψ (repr (raw_gfactors pt)) ⊢ WP hl_gfactors (repr pt) @ E [{ Ψ }].
Proof.
have reprS : ∀ pt' : PreTerm.pre_term,
    repr ([pt'], @nil PreTerm.pre_term) =
    (InjRV (repr pt', InjLV #()), InjLV #())%V.
  by move=> pt'; rewrite /= [@repr_list]unlock.
iIntros "HΨ"; wp_lam.
wp_apply twp_hl_is_gmul.
rewrite /raw_gfactors.
case: pt => [o|o t|o t1 t2|[|] ps ns]; wp_pures.
all: try (rewrite /CONS; wp_pures; iEval (rewrite reprS) in "HΨ";
          by iApply "HΨ").
by rewrite -!repr_list_val; iApply "HΨ".
Qed.

(** ** Smart constructors *)

Lemma twp_hl_mul_aux E (s : SMS.sms PreTerm.pre_term) Ψ :
  Ψ (repr (PreTerm.mul_aux s)) ⊢ WP hl_mul_aux (repr s) @ E [{ Ψ }].
Proof.
rewrite repr_smsE /PreTerm.mul_aux /SMS.pos /SMS.neg.
case: (SMS.car s) => [ps ns] /=; iIntros "HΨ"; wp_lam.
have mulE : (#TOpN_tag, (#TMul_tag, repr_list ps, repr_list ns))%V =
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

Lemma twp_hl_gmul_aux E (s : SMS.sms PreTerm.pre_term) Ψ :
  Ψ (repr (PreTerm.gmul_aux s)) ⊢ WP hl_gmul_aux (repr s) @ E [{ Ψ }].
Proof.
rewrite repr_smsE /PreTerm.gmul_aux /SMS.pos /SMS.neg.
case: (SMS.car s) => [ps ns] /=; iIntros "HΨ"; wp_lam.
have mulE : (#TOpN_tag, (#TGMul_tag, repr_list ps, repr_list ns))%V =
            repr (PreTerm.PTGMul ps ns).
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
  Ψ (repr (SMS.Internal.flat f A)) ⊢ WP hl_flat fv (repr A) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; case: A => [ps ns]; rewrite /repr_prod /=; wp_lam; wp_pures.
wp_apply (twp_hl_bind_fst _ ns); wp_pures; wp_apply (twp_hl_bind_snd _ ps).
wp_apply twp_append_lists; wp_pures.
wp_apply (twp_hl_bind_snd _ ns); wp_pures; wp_apply (twp_hl_bind_fst _ ps).
wp_apply twp_append_lists.
by wp_pures; iApply "HΨ".
Qed.

End Flat.

Lemma twp_leq_pre_term_le pt1 pt2 E Ψ :
  Ψ #(bool_decide (SMS.Internal.le pt1 pt2)) ⊢
  WP (leq_term (repr pt1) (repr pt2)) @ E [{ Ψ }].
Proof.
rewrite (bool_decide_ext _ _ (iff_sym (pt_order_lexico pt1 pt2))).
exact: twp_leq_pre_term.
Qed.

Lemma car_bind_factors A :
  (∀ x, x ∈ SMS.Internal.elements A → PreTerm.wf x) →
  SMS.car (SMS.bind PreTerm.factors (SMS.make A.1 A.2)) =
  SMS.Internal.to SMS.Internal.le (SMS.Internal.flat raw_factors A).
Proof.
move=> wfA; rewrite SMS.car_bind SMS.car_make; apply/SMS.Internal.to_eq => z.
rewrite SMS.Internal.count_flat_to -surjective_pairing.
congr SMS.Internal.count; apply: SMS.Internal.flat_ext => x x_A.
by rewrite PreTerm.car_factorsE //; apply: wfA.
Qed.

Lemma car_bind_gfactors A :
  (∀ x, x ∈ SMS.Internal.elements A → PreTerm.wf x) →
  SMS.car (SMS.bind PreTerm.gfactors (SMS.make A.1 A.2)) =
  SMS.Internal.to SMS.Internal.le (SMS.Internal.flat raw_gfactors A).
Proof.
move=> wfA; rewrite SMS.car_bind SMS.car_make; apply/SMS.Internal.to_eq => z.
rewrite SMS.Internal.count_flat_to -surjective_pairing.
congr SMS.Internal.count; apply: SMS.Internal.flat_ext => x x_A.
by rewrite PreTerm.car_gfactorsE //; apply: wfA.
Qed.

Lemma twp_hl_normalize_factors E A Ψ :
  Ψ (repr (SMS.Internal.to SMS.Internal.le (SMS.Internal.flat raw_factors A)))
  ⊢ WP hl_normalize_factors (repr A) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam.
wp_apply (twp_hl_flat raw_factors _ twp_hl_factors).
wp_apply (twp_sms_to SMS.Internal.le eq_term leq_term twp_eq_pre_term
            twp_leq_pre_term_le).
by iApply "HΨ".
Qed.

Lemma twp_hl_normalize_gfactors E A Ψ :
  Ψ (repr (SMS.Internal.to SMS.Internal.le (SMS.Internal.flat raw_gfactors A)))
  ⊢ WP hl_normalize_gfactors (repr A) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam.
wp_apply (twp_hl_flat raw_gfactors _ twp_hl_gfactors).
wp_apply (twp_sms_to SMS.Internal.le eq_term leq_term twp_eq_pre_term
            twp_leq_pre_term_le).
by iApply "HΨ".
Qed.

Lemma twp_hl_mul_pair E A Ψ :
  (∀ x, x ∈ SMS.Internal.elements A → PreTerm.wf x) →
  Ψ (repr (PreTerm.mul (SMS.make A.1 A.2))) ⊢
  WP hl_mul_pair (repr A) @ E [{ Ψ }].
Proof.
move=> wfA; iIntros "HΨ"; wp_lam.
wp_apply twp_hl_normalize_factors.
rewrite -(car_bind_factors A wfA).
wp_apply (twp_hl_mul_aux _ (SMS.bind PreTerm.factors (SMS.make A.1 A.2))).
by iApply "HΨ".
Qed.

Lemma twp_hl_gmul_pair E A Ψ :
  (∀ x, x ∈ SMS.Internal.elements A → PreTerm.wf x) →
  Ψ (repr (PreTerm.gmul (SMS.make A.1 A.2))) ⊢
  WP hl_gmul_pair (repr A) @ E [{ Ψ }].
Proof.
move=> wfA; iIntros "HΨ"; wp_lam.
wp_apply twp_hl_normalize_gfactors.
rewrite -(car_bind_gfactors A wfA).
wp_apply (twp_hl_gmul_aux _ (SMS.bind PreTerm.gfactors (SMS.make A.1 A.2))).
by iApply "HΨ".
Qed.

Lemma twp_hl_mul E pt1 pt2 Ψ :
  PreTerm.wf pt1 → PreTerm.wf pt2 →
  Ψ (repr (PreTerm.mul (SMS.make [pt1; pt2] []))) ⊢
  WP hl_mul (repr pt1) (repr pt2) @ E [{ Ψ }].
Proof.
move=> wf1 wf2; iIntros "HΨ"; wp_lam; wp_pures; rewrite /CONS; wp_pures.
rewrite (_ : (InjRV (val_of_pre_term pt1,
                     InjRV (val_of_pre_term pt2, [])), [])%V =
             repr ([pt1; pt2], @nil PreTerm.pre_term)); last first.
  by rewrite /= [@repr_list]unlock.
wp_apply twp_hl_mul_pair; last by iApply "HΨ".
by move=> x; rewrite /SMS.Internal.elements /= elem_of_cons
  list_elem_of_singleton => -[->|->].
Qed.

Lemma twp_hl_gmul E pt1 pt2 Ψ :
  PreTerm.wf pt1 → PreTerm.wf pt2 →
  Ψ (repr (PreTerm.gmul (SMS.make [pt1; pt2] []))) ⊢
  WP hl_gmul (repr pt1) (repr pt2) @ E [{ Ψ }].
Proof.
move=> wf1 wf2; iIntros "HΨ"; wp_lam; wp_pures; rewrite /CONS; wp_pures.
rewrite (_ : (InjRV (val_of_pre_term pt1,
                     InjRV (val_of_pre_term pt2, [])), [])%V =
             repr ([pt1; pt2], @nil PreTerm.pre_term)); last first.
  by rewrite /= [@repr_list]unlock.
wp_apply twp_hl_gmul_pair; last by iApply "HΨ".
by move=> x; rewrite /SMS.Internal.elements /= elem_of_cons
  list_elem_of_singleton => -[->|->].
Qed.

Lemma twp_hl_inv E pt Ψ :
  PreTerm.wf pt →
  Ψ (repr (PreTerm.mul (SMS.make [] [pt]))) ⊢ WP hl_inv (repr pt) @ E [{ Ψ }].
Proof.
move=> wf_pt; iIntros "HΨ"; wp_lam; wp_pures; rewrite /CONS; wp_pures.
rewrite (_ : ([], InjRV (val_of_pre_term pt, []))%V =
             repr (@nil PreTerm.pre_term, [pt])); last first.
  by rewrite /= [@repr_list]unlock.
wp_apply twp_hl_mul_pair; last by iApply "HΨ".
by move=> x; rewrite /SMS.Internal.elements /= list_elem_of_singleton => ->.
Qed.

Lemma twp_hl_ginv E pt Ψ :
  PreTerm.wf pt →
  Ψ (repr (PreTerm.gmul (SMS.make [] [pt]))) ⊢ WP hl_ginv (repr pt) @ E [{ Ψ }].
Proof.
move=> wf_pt; iIntros "HΨ"; wp_lam; wp_pures; rewrite /CONS; wp_pures.
rewrite (_ : ([], InjRV (val_of_pre_term pt, []))%V =
             repr (@nil PreTerm.pre_term, [pt])); last first.
  by rewrite /= [@repr_list]unlock.
wp_apply twp_hl_gmul_pair; last by iApply "HΨ".
by move=> x; rewrite /SMS.Internal.elements /= list_elem_of_singleton => ->.
Qed.

Lemma twp_hl_mk_exp E (b e : PreTerm.pre_term) Ψ :
  Ψ (repr (PreTerm.mk_exp b e)) ⊢ WP hl_mk_exp (repr b) (repr e) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam; wp_pures; rewrite hl_oneE.
wp_apply twp_eq_pre_term.
rewrite /PreTerm.mk_exp.
by case: (bool_decide (e = PreTerm.PTMul [] [])); wp_pures; iApply "HΨ".
Qed.

Lemma twp_hl_exp_aux E (b e : PreTerm.pre_term) Ψ :
  PreTerm.wf b → PreTerm.wf e →
  Ψ (repr (PreTerm.exp_aux b e)) ⊢ WP hl_exp_aux (repr b) (repr e) @ E [{ Ψ }].
Proof.
move=> wf_b wf_e; iIntros "HΨ"; wp_lam; wp_pures; rewrite /CONS; wp_pures.
wp_apply twp_hl_expo; wp_pures.
rewrite (_ : (InjRV (repr (PreTerm.expo b),
                     InjRV (val_of_pre_term e, [])), [])%V =
             repr ([PreTerm.expo b; e], @nil PreTerm.pre_term)); last first.
  by rewrite /= [@repr_list]unlock.
wp_apply twp_hl_mul_pair.
  move=> x; rewrite /SMS.Internal.elements /= elem_of_cons.
  by rewrite list_elem_of_singleton => -[->|->] //; exact: PreTerm.wf_expo.
wp_apply twp_hl_base.
wp_apply twp_hl_mk_exp.
by iApply "HΨ".
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
have mapE : ∀ T (f : PreTerm.pre_term -> T) (l : list PreTerm.pre_term),
    map f l = f <$> l.
  by move=> T f; elim=> [//|x l IH] /=; rewrite IH.
iIntros "HΨ"; wp_lam; wp_pures.
wp_apply twp_hl_gfactors.
have rawE : raw_gfactors b = SMS.car (PreTerm.gfactors b).
  by rewrite PreTerm.car_gfactorsE.
rewrite /PreTerm.exp SMS.map_pos_neg /SMS.pos /SMS.neg rawE.
have elemE x : x ∈ (SMS.car (PreTerm.gfactors b)).1 ∨
               x ∈ (SMS.car (PreTerm.gfactors b)).2 → x ∈ PreTerm.gfactors b.
  by rewrite -SMS.elem_of_elements SMS.elements_car elem_of_app.
case: (SMS.car (PreTerm.gfactors b)) elemE => [ps ns] /= elemE.
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
wp_apply twp_hl_gmul_pair; last by iApply "HΨ".
move=> x; rewrite /SMS.Internal.elements /= elem_of_app.
case=> /list_elem_of_fmap [u [-> u_in]];
  (apply: PreTerm.wf_exp_aux => //;
     [apply: (PreTerm.wf_gfactors_wf wfg)
     |apply: (PreTerm.wf_gfactors_Ngmul wfg)];
     apply: elemE; by [left|right]).
Qed.

End Proofs.
