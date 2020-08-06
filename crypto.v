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

Section Keys.

Class key2SG Σ := KeySG {
  key_inG :> inG Σ (authR (gsetUR (prodO locO locO)));
  key2_symbol : gname;
  key1_symbol : gname;
  key_name : gname;
}.

Context `{symbolSG Σ, keySG Σ}.

Implicit Types LL : gsetUR (prodO locO locO).
Implicit Types ll : prodO locO locO.
Implicit Types Lb : gsetUR (prodO boolO locO).
Implicit Types l : locO.

Definition key_inv : iProp Σ :=
  ∃ LL,
    own key_name (● LL) ∗
    ⌜perm LL⌝ ∗
    ([∗ set] ll ∈ LL, symbol true  key2_symbol ll.1 ∗
                      symbol false key2_symbol ll.2).

Definition key l1 l2 : iProp Σ :=
  own key_name (◯ {[l1, l2]}).

Global Instance key_persistent l1 l2 : Persistent (key l1 l2).
Proof. apply _. Qed.

Lemma key_permR l1 l21 l22 :
  key_inv -∗ key l1 l21 -∗ key l1 l22 -∗ ⌜l21 = l22⌝.
Proof.
iDestruct 1 as (LL) "(Hown & %Hperm & Halloc)".
iIntros "Hl21 Hl22"; rewrite /key.
iPoseProof (own_valid_2 with "Hown Hl21") as "%Hvalid1".
rewrite auth_both_valid in Hvalid1 *; case=> Hvalid1 _.
iPoseProof (own_valid_2 with "Hown Hl22") as "%Hvalid2".
rewrite auth_both_valid in Hvalid2 *; case=> Hvalid2 _.
have {}Hvalid1: (l1, l21) ∈ LL.
  move/gset_included in Hvalid1; apply: Hvalid1.
  by apply elem_of_singleton_2.
have {}Hvalid2: (l1, l22) ∈ LL.
  move/gset_included in Hvalid2; apply: Hvalid2.
  by apply elem_of_singleton_2.
by iPureIntro; apply (Hperm _ _ Hvalid1 Hvalid2).
Qed.

Lemma key_permL l11 l12 l2 :
  key_inv -∗ key l11 l2 -∗ key l12 l2 -∗ ⌜l11 = l12⌝.
Proof.
iDestruct 1 as (LL) "(Hown & %Hperm & Halloc)".
rewrite /key; iIntros "Hl11 Hl12".
iPoseProof (own_valid_2 with "Hown Hl11") as "%Hvalid1".
iPoseProof (own_valid_2 with "Hown Hl12") as "%Hvalid2".
move: Hvalid1; rewrite auth_both_valid; case=> Hvalid1 _.
move: Hvalid2; rewrite auth_both_valid; case=> Hvalid2 _.
have {}Hvalid1 : (l11, l2) ∈ LL.
  move/gset_included in Hvalid1; apply: Hvalid1.
  by apply elem_of_singleton_2.
have {}Hvalid2 : (l12, l2) ∈ LL.
  move/gset_included in Hvalid2; apply: Hvalid2.
  by apply elem_of_singleton_2.
by iPureIntro; apply (Hperm _ _ Hvalid1 Hvalid2).
Qed.

End Keys.

Section Terms.

Context `{heapG Σ, cfgSG Σ, symbolSG Σ}.

Implicit Types s : side.

Definition lo_nonce : symbol_kind := 1%positive.
Definition hi_nonce : symbol_kind := 2%positive.
Definition lo_key   : symbol_kind := 3%positive.
Definition hi_key   : symbol_kind := 4%positive.

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
  term_inG  :> inG Σ (authR (gsetUR (prodO valO valO)));
  term_name :  gname
}.

Section Terms.

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
