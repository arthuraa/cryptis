From mathcomp Require Import ssreflect.
From iris.algebra Require Import excl auth frac agree gmap list.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import language.
From iris.program_logic Require Import lifting.
From iris.algebra Require Import gmap auth gset numbers excl agree ofe.
From iris.heap_lang Require Import notation proofmode metatheory.
From iris.heap_lang Require Import primitive_laws.
From iris.base_logic.lib Require Import invariants.
From iris_string_ident Require Import ltac2_string_ident.
From crypto Require Import basic symbols.

Section Terms.

Context `{heapG Σ, cfgSG Σ, symbolSG Σ}.

Inductive term  :=
| TInt of Z
| TPair of term & term
| TNonce of loc
| TKey of loc
| TEnc of loc & term.

Global Instance term_eq_dec : EqDecision term.
Proof.
refine (
  fix go t1 t2 {struct t1} : Decision (t1 = t2) :=
    match t1, t2 with
    | TInt n1, TInt n2 =>
      cast_if (decide (n1 = n2))
    | TPair t11 t12, TPair t21 t22  =>
      cast_if_and (decide (t11 = t21)) (decide (t12 = t22))
    | TNonce l1, TNonce l2 =>
      cast_if (decide (l1 = l2))
    | TKey l1, TKey l2 =>
      cast_if (decide (l1 = l2))
    | TEnc l1 t1, TEnc l2 t2 =>
      cast_if_and (decide (l1 = l2)) (decide (t1 = t2))
    | _, _ => right _
    end); clear go; abstract intuition congruence.
Defined.

Fixpoint val_of_term t : val :=
  match t with
  | TInt n => (#0, #n)
  | TPair t1 t2 => (#1, (val_of_term t1, val_of_term t2))%V
  | TNonce l => (#2, #l)%V
  | TKey l => (#3, #l)%V
  | TEnc l t => (#4, (#l, val_of_term t))
  end.

Class termSG := TermSG {
  term_inG :> inG Σ (authR (gsetUR (prodO valO valO)));
  hi_key_name : gname;
  lo_key_name : gname;
  hi_nonce_name : gname;
  lo_nonce_name : gname;
  term_name : gname;
}.

Context `{termSG}.

Definition wf_nonce s l : iProp Σ :=
  symbol1 lo_nonce_name s l ∨
  symbol1 hi_nonce_name s l.
Global Instance persistent_wf_nonce s l : Persistent (wf_nonce s l).
Proof. apply _. Qed.

Definition wf_key s l : iProp Σ :=
  symbol1 lo_key_name s l ∨
  symbol1 hi_key_name s l.
Global Instance persistent_wf_key s l : Persistent (wf_key s l).
Proof. apply _. Qed.

(* Holds iff all the symbols that appear in the term have been allocated. *)
Fixpoint wf_term s t : iProp Σ :=
  match t with
  | TInt _ => True%I
  | TPair t1 t2 => wf_term s t1 ∗ wf_term s t2
  | TNonce l => wf_nonce s l
  | TKey l => wf_key s l
  | TEnc l t => wf_key s l ∗ wf_term s t
  end.
Global Instance persistent_wf_term s t : Persistent (wf_term s t).
Proof. elim: t=> /=; apply _. Qed.

(* Opaque terms are those that cannot be inspected by the attacker. *)
Definition opaque1 s t : iProp Σ :=
  match t with
  | TInt _ => False%I
  | TPair _ _ => False%I
  | TNonce l => symbol1 lo_nonce_name s l
  | TKey l => False%I
  | TEnc l t => symbol1 hi_key_name s l ∗ wf_term s t
  end.

Global Instance persistent_opaque1 s t : Persistent (opaque1 s t).
Proof. elim: t=> /=; apply _. Qed.

Lemma opaque1_wf_term s t : opaque1 s t -∗ wf_term s t.
Proof.
case: t=> /=.
- by iIntros (_) "?".
- by iIntros (??) "?".
- by iIntros (?) "?"; iLeft.
- by iIntros (?) "?".
- by iIntros (??) "[??]"; iFrame.
Qed.

Implicit Types TT : gsetUR (prodO valO valO).

Definition opaque_inv : iProp Σ :=
  ∃ TT, own term_name (● TT)
        ∗ ⌜perm TT⌝
        ∗ (∀ v1 v2, ⌜(v1, v2) ∈ TT⌝ -∗
           ∃ t1 t2, ⌜v1 = val_of_term t1⌝ ∗
                    ⌜v2 = val_of_term t2⌝ ∗
                    opaque1 true t1 ∗ opaque1 false t2).

Definition opaque v1 v2 : iProp Σ :=
  own term_name (◯ {[v1, v2]}).

Global Instance persistent_opaque v1 v2 : Persistent (opaque v1 v2).
Proof. apply _. Qed.

Fixpoint lo_term_aux t1 t2 : iProp Σ :=
  opaque (val_of_term t1) (val_of_term t2) ∨
  match t1, t2 with
  | TInt n1, TInt n2 => ⌜n1 = n2⌝
  | TPair t11 t12, TPair t21 t22 =>
    lo_term_aux t11 t21 ∗ lo_term_aux t12 t22
  | TNonce l1, TNonce l2 =>
    symbol lo_nonce_name (LR l1 l2)
  | TKey l1, TKey l2 =>
    symbol lo_key_name (LR l1 l2)
  | TEnc l1 t1, TEnc l2 t2 =>
    symbol lo_key_name (LR l1 l2) ∗ lo_term_aux t1 t2
  | _, _ => False%I
  end.

Global Instance persistent_lo_term_aux t1 t2 : Persistent (lo_term_aux t1 t2).
Proof.
elim: t1 t2=> /=.
- by move=> ?; case=> *; apply _.
- by move=> ????; case=> *; apply _.
- by move=> ?; case=> *; apply _.
- by move=> ?; case=> *; apply _.
- by move=> ???; case=> *; apply _.
Qed.

Definition lo_term v1 v2 : iProp Σ :=
  ∃ t1 t2, ⌜v1 = val_of_term t1⌝ ∗
           ⌜v2 = val_of_term t2⌝ ∗
           lo_term_aux t1 t2.

Global Instance persistent_lo_term v1 v2 : Persistent (lo_term v1 v2).
Proof. apply _. Qed.

Definition eq_term : val := (rec: "eq" "x" "y" :=
  if: (Fst "x" = #0) && (Fst "y" = #0) then
    Snd "x" = Snd "y"
  else if: (Fst "x" = #1) && (Fst "y" = #1) then
    ("eq" (Fst (Snd "x")) (Fst (Snd "y"))) &&
    ("eq" (Snd (Snd "x")) (Snd (Snd "y")))
  else if: (Fst "x" = #2) && (Fst "y" = #2) then
    Snd "x" = Snd "y"
  else if: (Fst "x" = #3) && (Fst "y" = #3) then
    Snd "x" = Snd "y"
  else if: (Fst "x" = #4) && (Fst "y" = #4) then
    (Fst (Snd "x") = Fst (Snd "y")) &&
    ("eq" (Snd (Snd "x")) (Snd (Snd "y")))
  else #false)%V.

Lemma wp_eq_term t1 t2 :
  ⊢ WP (eq_term (val_of_term t1) (val_of_term t2)) {{ v,
      ⌜v = #(bool_decide (t1 = t2))⌝ }}.
Proof.
iLöb as "IH" forall (t1 t2).
case: t1=> [n1|t11 t12|l1|l1|l1 t1];
case: t2=> [n2|t21 t22|l2|l2|l2 t2] /=;
wp_rec; wp_pures=> //.
- iPureIntro; congr (# (LitBool _)).
  apply: bool_decide_iff; intuition congruence.
- wp_bind (eq_term _ _).
  iApply (wp_wand with "IH"); iIntros (?) "->".
  case: bool_decide_reflect=> e1.
  + wp_pures; iApply (wp_wand with "IH"); iIntros (?) "->".
    iPureIntro; congr (# (LitBool _)).
    apply: bool_decide_iff; intuition congruence.
  + wp_pures; iPureIntro; congr (# (LitBool _)).
    rewrite bool_decide_false; congruence.
- iPureIntro; congr (# (LitBool _)).
  apply: bool_decide_iff; intuition congruence.
- iPureIntro; congr (# (LitBool _)).
  apply: bool_decide_iff; intuition congruence.
- case: bool_decide_reflect=> e1.
  + wp_pures; iApply (wp_wand with "IH"); iIntros (?) "->".
    iPureIntro; congr (# (LitBool _)).
    apply: bool_decide_iff; intuition congruence.
  + wp_pures; iPureIntro; congr (# (LitBool _)).
    rewrite bool_decide_false; congruence.
Qed.

Definition ty_nonce v1 v2 : iProp Σ :=
  symbol lo_nonce v1 v2 ∨ symbol hi_nonce v1 v2.

Definition ty_hi_nonce v1 v2 : iProp Σ :=
  symbol hi_nonce v1 v2.

Definition ty_key v1 v2 : iProp Σ :=
  symbol lo_key v1 v2 ∨ symbol hi_key v1 v2.

Definition ty_hi_key v1 v2 : iProp Σ :=
  symbol hi_key v1 v2.

Definition ty1 (ty : val → val → iProp Σ) left v : iProp Σ :=
  ∃ v', if left then ty v v' else ty v' v.

Definition ty_key1 := ty1 ty_key.
Definition ty_hi_key1 := ty1 ty_hi_key.
Definition ty_nonce1 := ty1 ty_nonce.
Definition ty_hi_nonce1 := ty1 ty_hi_nonce.
