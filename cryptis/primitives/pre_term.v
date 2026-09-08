(* HeapLang implementations of the pre-term operations of
   [core/pre_term/normalize.v], together with specs saying that each program
   computes the corresponding pure function.

   Every pure function of [normalize.v] has a counterpart here:

     is_inv / is_exp / is_mul / is_nonce   ->  hl_is_inv / hl_is_exp /
                                               hl_is_mul / hl_is_nonce
     base / expo / factors                 ->  hl_base / hl_expo / hl_factors
     inv_aux / mul_aux                     ->  hl_inv_aux / hl_mul_aux
     normalize_factors                     ->  hl_normalize_factors
     mul / inv                             ->  hl_mul_list / hl_inv
     exp_aux / exp                         ->  hl_exp_aux / hl_exp

   [normalize] itself is not implemented: the HeapLang layer only ever builds
   pre-terms with the smart constructors, so it never needs to renormalise.

   The product machinery is not reimplemented here.  [normalize_factors] is
   [SMS.to pt_order inv_aux] applied to the flattened factor lists, so
   [hl_normalize_factors] is just [sms_to] from [primitives/sms.v] instantiated
   at [pt_order]/[PreTerm.inv_aux], and its spec is [twp_sms_to].

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
    else (* Hash / Inv *) #true
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
      eq_list "eq" (Snd "x") (Snd "y")
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
    else #true (* Hash / Inv *)
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
      leq_list eq_term "loop" "a1" "a2"
    else #false
  else #false)%V.

(** ** Recognisers *)

Definition hl_is_inv : val := λ: "pt",
  if: Fst "pt" = #TOp1_tag then Fst (Fst (Snd "pt")) = #TInv_tag else #false.

Definition hl_is_exp : val := λ: "pt",
  if: Fst "pt" = #TOp2_tag then Fst (Fst (Snd "pt")) = #TExp_tag else #false.

Definition hl_is_mul : val := λ: "pt", Fst "pt" = #TMul_tag.

Definition hl_is_nonce : val := λ: "pt",
  if: Fst "pt" = #TOp0_tag then Fst (Snd "pt") = #TNonce_tag else #false.

(** ** Destructors *)

(* [repr (PreTerm.PTMul [])], i.e. the unit of the product. *)
Definition hl_one : val := (#TMul_tag, NILV)%V.

Definition hl_base : val := λ: "pt",
  if: hl_is_exp "pt" then Snd (Fst (Snd "pt")) else "pt".

Definition hl_expo : val := λ: "pt",
  if: hl_is_exp "pt" then Snd (Snd "pt") else hl_one.

Definition hl_factors : val := λ: "pt",
  if: hl_is_mul "pt" then Snd "pt" else "pt" :: NILV.

(** ** Smart constructors *)

Definition hl_inv_aux : val := λ: "pt",
  if: hl_is_inv "pt" then Snd (Snd "pt")
  else (#TOp1_tag, (#TInv_tag, #(), "pt")).

Definition hl_mul_aux : val := λ: "c",
  match: "c" with
    NONE => hl_one
  | SOME "x" =>
      match: Snd "x" with
        NONE => Fst "x"
      | SOME <> => (#TMul_tag, "c")
      end
  end.

(* [mbind PreTerm.factors]: flatten the factor lists of a list of pre-terms. *)
Definition hl_all_factors : val := λ: "ts",
  foldr_list (λ: "t" "acc", append_lists (hl_factors "t") "acc") [] "ts".

(* [PreTerm.normalize_factors] = [SMS.to pt_order inv_aux] of the flattened
   factors, so this is [sms_to] at the pre-term instance. *)
Definition hl_normalize_factors : val := λ: "ts",
  sms_to leq_term eq_term hl_inv_aux (hl_all_factors "ts").

Definition hl_mul_list : val := λ: "ts",
  hl_mul_aux (hl_normalize_factors "ts").

Definition hl_mul : val := λ: "t1" "t2", hl_mul_list ("t1" :: "t2" :: NILV).

Definition hl_inv : val := λ: "t",
  if: hl_is_mul "t" then hl_mul_list (map_list hl_inv_aux (hl_factors "t"))
  else hl_inv_aux "t".

Definition hl_exp_aux : val := λ: "b" "e",
  if: eq_term "e" hl_one then "b" else (#TOp2_tag, (#TExp_tag, "b", "e")).

Definition hl_exp : val := λ: "b" "e",
  hl_exp_aux (hl_base "b") (hl_mul_list (hl_expo "b" :: "e" :: NILV)).

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
case: o1 o2 => [o1||] [o2||] /=. all: wp_lam; wp_pures => //.
iApply twp_wand; first wp_apply twp_eq_key_type.
iIntros (?) "->". iPureIntro.
congr (# (LitBool _)). apply: bool_decide_ext.
intuition congruence.
Qed.

Lemma twp_eq_term_op2 E (o1 o2 : term_op2) :
  ⊢ WP (eq_term_op2 (repr o1) (repr o2)) @ E
    [{ v, ⌜v = #(bool_decide (o1 = o2))⌝}].
Proof. case: o1 o2 => [] [] /=; wp_lam; wp_pures => //. Qed.

Lemma twp_eq_pre_term_aux E pt1 pt2 :
  ⊢ WP (eq_term (repr pt1) (repr pt2)) @ E
       [{ v, ⌜v = #(bool_decide (pt1 = pt2))⌝ }].
Proof.
elim: pt1 pt2 => [o1|o1 t1 IH1|o1 t11 IH1 t12 IH2|ts1 IHts1];
case=> [o2|o2 t2|o2 t21 t22|ts2]; wp_rec; wp_pures=> //.
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
  iApply (@twp_eq_list PreTerm.pre_term); last first.
    iPureIntro; congr (# (LitBool _)); apply: bool_decide_ext.
    by split; congruence.
  elim: ts1 IHts1 => //= [|x1 ts1 IH].
    by move=> *; exfalso; set_solver.
  case=> IHx1 /IH IHts1 x1' x2' Ψ.
  rewrite elem_of_cons; case=> [->|x1'_in]; iIntros "post"; last first.
    by iApply IHts1.
  iApply twp_wand; first iApply IHx1; by iIntros (?) "->".
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
case: o1 o2 => [k1||] [k2||] /=; wp_lam; wp_pures => //.
iApply twp_wand; first by wp_apply twp_leq_key_type.
by iIntros (?) "->".
Qed.

Lemma twp_leq_term_op2 E (o1 o2 : term_op2) :
  ⊢ WP (leq_term_op2 (repr o1) (repr o2)) @ E [{ v, ⌜v = #(op2_le o1 o2)⌝}].
Proof. by case: o1 o2 => [] [] /=; wp_lam; wp_pures. Qed.

Lemma twp_leq_pre_term pt1 pt2 E Ψ :
  Ψ #(bool_decide (pt_order pt1 pt2)) ⊢
  WP (leq_term (repr pt1) (repr pt2)) @ E [{ Ψ }].
Proof.
elim: pt1 pt2 Ψ => [o1|o1 t1 IH1|o1 t11 IH1 t12 IH2|ts1 IHts1];
case => [o2|o2 t2|o2 t21 t22|ts2] Ψ;
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
rewrite -!repr_list_val.
iApply twp_leq_list => //.
- move=> x1 x2 Φ; iIntros "_ post".
  by iApply twp_eq_pre_term; iApply "post".
- elim: ts1 IHts1 => [|y ts1 IH] /=.
    by move=> _ x1 x2 /elem_of_nil.
  case=> IHy /IH IHts1 x1 x2; rewrite elem_of_cons => - [->|x1_in] Φ;
    iIntros "_ post".
  + iApply IHy; rewrite (bool_decide_ext _ _ (pt_order_lexico _ _)).
    by iApply "post".
  + by iApply (IHts1 x1 x2 x1_in with "[//] post").
- by iIntros "_".
Qed.

(** ** Recognisers *)

Lemma twp_hl_is_inv pt E Ψ :
  Ψ #(PreTerm.is_inv pt) ⊢ WP hl_is_inv (repr pt) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam.
case: pt => [o|o t|o t1 t2|ts] /=; wp_pures; try by iApply "HΨ".
by case: o => [k| |] /=; wp_pures; iApply "HΨ".
Qed.

Lemma twp_hl_is_exp pt E Ψ :
  Ψ #(PreTerm.is_exp pt) ⊢ WP hl_is_exp (repr pt) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam.
case: pt => [o|o t|o t1 t2|ts]; try by (wp_pures; iApply "HΨ").
all: by case: o; wp_pures; iApply "HΨ".
Qed.

Lemma twp_hl_is_mul pt E Ψ :
  Ψ #(PreTerm.is_mul pt) ⊢ WP hl_is_mul (repr pt) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam.
by case: pt => [o|o t|o t1 t2|ts] /=; wp_pures; iApply "HΨ".
Qed.

Lemma twp_hl_is_nonce pt E Ψ :
  Ψ #(PreTerm.is_nonce pt) ⊢ WP hl_is_nonce (repr pt) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam.
case: pt => [o|o t|o t1 t2|ts]; try by (wp_pures; iApply "HΨ").
all: by case: o => [n|a]; wp_pures; iApply "HΨ".
Qed.

(** ** Destructors *)

Lemma twp_hl_base pt E Ψ :
  Ψ (repr (PreTerm.base pt)) ⊢ WP hl_base (repr pt) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam.
wp_apply twp_hl_is_exp.
case: pt => [o|o t|o t1 t2|ts]; try by (wp_pures; iApply "HΨ").
all: by case: o; wp_pures; iApply "HΨ".
Qed.

Lemma twp_hl_expo pt E Ψ :
  Ψ (repr (PreTerm.expo pt)) ⊢ WP hl_expo (repr pt) @ E [{ Ψ }].
Proof.
have one : repr (PreTerm.PTMul []) = hl_one.
  by rewrite /= repr_list_unseal.
iIntros "HΨ"; wp_lam.
wp_apply twp_hl_is_exp.
rewrite /PreTerm.expo -?one.
case: pt => [o|o t|o t1 t2|ts]; try by (wp_pures; rewrite -?one; iApply "HΨ").
all: by case: o; wp_pures; rewrite -?one; iApply "HΨ".
Qed.

Lemma twp_hl_factors pt E Ψ :
  Ψ (repr (PreTerm.factors pt)) ⊢ WP hl_factors (repr pt) @ E [{ Ψ }].
Proof.
have reprS : forall pt' : PreTerm.pre_term,
    repr [pt'] = InjRV (repr pt', InjLV #()).
  by move=> pt'; rewrite repr_list_unseal.
iIntros "HΨ"; wp_lam.
wp_apply twp_hl_is_mul.
rewrite /PreTerm.factors.
case: pt => [o|o t|o t1 t2|ts]; wp_pures.
1-3: rewrite /CONS; wp_pures; iEval (rewrite reprS /=) in "HΨ"; by iApply "HΨ".
by rewrite -repr_list_val; iApply "HΨ".
Qed.

(** ** Smart constructors *)

Lemma twp_hl_inv_aux pt E Ψ :
  Ψ (repr (PreTerm.inv_aux pt)) ⊢ WP hl_inv_aux (repr pt) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam.
wp_apply twp_hl_is_inv.
case: pt => [o|o t|o t1 t2|ts]; try by (wp_pures; iApply "HΨ").
all: by case: o => [k| |]; wp_pures; iApply "HΨ".
Qed.

Lemma wp_hl_inv_aux E pt Ψ :
  Ψ (repr (PreTerm.inv_aux pt)) ⊢ WP hl_inv_aux (repr pt) @ E {{ Ψ }}.
Proof. iIntros "HΨ"; iApply twp_wp; by wp_apply twp_hl_inv_aux. Qed.

Lemma twp_hl_mul_aux E (ts : list PreTerm.pre_term) Ψ :
  Ψ (repr (PreTerm.mul_aux ts)) ⊢ WP hl_mul_aux (repr ts) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; rewrite /hl_mul_aux /hl_one; wp_lam.
case: ts => [|t [|u ts]]; rewrite {1}repr_list_unseal /=; wp_pures.
- iEval (rewrite repr_list_unseal /=) in "HΨ"; by iApply "HΨ".
- by iApply "HΨ".
- by rewrite [repr_list (t :: u :: ts)]repr_list_val; iApply "HΨ".
Qed.

Lemma twp_hl_all_factors E (ts : list PreTerm.pre_term) Ψ :
  Ψ (repr (mbind PreTerm.factors ts)) ⊢ WP hl_all_factors (repr ts) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam.
wp_pures; wp_apply twp_nil.
wp_apply (twp_foldr_list (λ (t : PreTerm.pre_term) (acc : list PreTerm.pre_term),
                           PreTerm.factors t ++ acc)) => //.
  iIntros "%b %a %Φ _ HΦ"; wp_pures.
  wp_apply twp_hl_factors.
  wp_apply twp_append_lists.
  by iApply "HΦ".
iIntros "_".
by iApply "HΨ".
Qed.

Lemma twp_hl_normalize_factors E (ts : list PreTerm.pre_term) Ψ :
  Ψ (repr (PreTerm.normalize_factors ts)) ⊢
  WP hl_normalize_factors (repr ts) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam.
wp_apply twp_hl_all_factors.
wp_apply (twp_sms_to pt_order PreTerm.inv_aux eq_term hl_inv_aux leq_term
            twp_eq_pre_term twp_hl_inv_aux twp_leq_pre_term).
by iApply "HΨ".
Qed.

Lemma twp_hl_mul_list E (ts : list PreTerm.pre_term) Ψ :
  Ψ (repr (PreTerm.mul ts)) ⊢ WP hl_mul_list (repr ts) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam.
wp_apply twp_hl_normalize_factors.
wp_apply twp_hl_mul_aux.
by iApply "HΨ".
Qed.

Lemma twp_hl_mul E pt1 pt2 Ψ :
  Ψ (repr (PreTerm.mul [pt1; pt2])) ⊢ WP hl_mul (repr pt1) (repr pt2) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam; wp_pures.
wp_apply twp_nil.
wp_apply twp_cons.
wp_apply twp_cons.
wp_apply twp_hl_mul_list.
by iApply "HΨ".
Qed.

Lemma twp_hl_inv E pt Ψ :
  Ψ (repr (PreTerm.inv pt)) ⊢ WP hl_inv (repr pt) @ E [{ Ψ }].
Proof.
have invS : forall pt' : PreTerm.pre_term,
    [[{ True }]] hl_inv_aux (repr pt') @ E [[{ RET repr (PreTerm.inv_aux pt'); True }]].
  by iIntros "%pt' %Φ _ HΦ"; wp_apply twp_hl_inv_aux; iApply "HΦ".
have mapE : forall T (f : PreTerm.pre_term -> T) (l : list PreTerm.pre_term),
    map f l = f <$> l.
  by move=> T f; elim=> [//|x l IH] /=; rewrite IH.
have invE : PreTerm.is_mul pt = true ->
    PreTerm.inv pt = PreTerm.mul (PreTerm.inv_aux <$> PreTerm.factors pt).
  by case: pt.
iIntros "HΨ"; wp_lam.
wp_apply twp_hl_is_mul.
case Em: (PreTerm.is_mul pt); wp_pures.
- rewrite (invE Em).
  wp_apply twp_hl_factors.
  wp_apply (twp_map_list PreTerm.inv_aux hl_inv_aux) => //.
    by apply/Forall_forall => x _; exact: invS.
  iIntros "_"; rewrite mapE.
  wp_apply twp_hl_mul_list.
  by iApply "HΨ".
- rewrite PreTerm.inv_Nmul; last by rewrite Em.
  by wp_apply twp_hl_inv_aux; iApply "HΨ".
Qed.

Lemma twp_hl_exp_aux E (b e : PreTerm.pre_term) Ψ :
  Ψ (repr (PreTerm.exp_aux b e)) ⊢ WP hl_exp_aux (repr b) (repr e) @ E [{ Ψ }].
Proof.
have one : hl_one = repr (PreTerm.PTMul []).
  by rewrite /hl_one /= repr_list_unseal.
iIntros "HΨ"; wp_lam; wp_pures; rewrite one.
wp_apply twp_eq_pre_term.
rewrite /PreTerm.exp_aux.
by case: (bool_decide (e = PreTerm.PTMul [])); wp_pures; iApply "HΨ".
Qed.

Lemma twp_hl_exp E (b e : PreTerm.pre_term) Ψ :
  Ψ (repr (PreTerm.exp b e)) ⊢ WP hl_exp (repr b) (repr e) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam; wp_pures.
wp_apply twp_nil.
wp_apply twp_cons.
wp_apply twp_hl_expo.
wp_apply twp_cons.
wp_apply twp_hl_mul_list.
wp_apply twp_hl_base.
wp_apply twp_hl_exp_aux.
by iApply "HΨ".
Qed.

End Proofs.

