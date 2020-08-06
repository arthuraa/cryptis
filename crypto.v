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
From crypto Require Import basic.

Section Terms.

Context `{heapG Σ, cfgSG Σ, symbolSG Σ, symbol2SG Σ}.

Inductive term  :=
| TInt of Z
| TPair of term & term
| TNonce of loc
| TKey of loc
| TEnc of loc & term.

Fixpoint val_of_term t : val :=
  match t with
  | TInt n => (#0, #n)
  | TPair t1 t2 => (#1, (val_of_term t1, val_of_term t2))%V
  | TNonce l => (#2, #l)%V
  | TKey l => (#3, #l)%V
  | TEnc l t => (#4, (#l, val_of_term t))
  end.

Class termSG := TermSG {
  term_inG    :> inG Σ (authR (gsetUR (prodO valO valO)));
  key_name    :  gname;
  key2_name   :  gname;
  nonce_name  :  gname;
  nonce2_name :  gname;
  term_name   :  gname;
}.

Context `{termSG}.




Fixpoint opaque s t : iProp Σ :=
  match t with
  | TInt _ => False%I
  | TPair _ _ => False%I
  | TNonce l => symbol s lo_nonce l
  | TKey l => False%I
  | TEnc l t => symbol s hi_key l
  end.

Implicit Types TT : gsetUR (prodO valO valO).

Definition opaque_inv : iProp Σ :=
  ∃ TT, own term_name (● TT)
        ∗ (∀ v1 v2, ⌜(v1, v2) ∈ TT⌝ -∗
           ∃ t1 t2, ⌜v1 = val_of_term t1⌝ ∗
                    ⌜v2 = val_of_term t2⌝ ∗
                    opaque Left t1 ∗ opaque Right t2).

Fixpoint lo_term' t1 t2 : iProp Σ :=
  own term_name (◯ {[val_of_term t1, val_of_term t2]}) ∨
  match t1, t2 with
  | TInt n1, TInt n2 => ⌜n1 = n2⌝
  | TPair t11 t12, TPair t21 t22 =>
    lo_term' t11 t21 ∗ lo_term' t12 t22
  | TNonce l1, TNonce l2 =>
    symbol lo_nonce #l1 #l2
  | TKey l1, TKey l2 =>
    symbol lo_key #l1 #l2
  | TEnc l1 t1, TEnc l2 t2 =>
    symbol lo_key #l1 #l2 ∗ lo_term' t1 t2
  | _, _ => False%I
  end.




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
