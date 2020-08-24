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
From crypto Require Import lib basic.
Import uPred.

Section Matching.

Context `{!EqDecision T, !Countable T}.

Inductive matching := L of T | R of T | LR of T & T.
Canonical matchingO := leibnizO matching.

Global Instance matching_dec : EqDecision matching.
Proof.
  refine (λ rl1 rl2,
            match rl1, rl2 with
            | L l1, L l2 =>
              if decide (l1 = l2) then _ else _
            | R l1, R l2 =>
              if decide (l1 = l2) then _ else _
            | LR l11 l12, LR l21 l22 =>
              if decide (l11 = l21) then
                if decide (l12 = l22) then _ else _
              else _
            | _, _ => _
            end); try by [left; congruence|right; congruence].
Defined.

Global Instance matching_countable : Countable matching.
Proof.
apply
  (inj_countable (λ rl, match rl with
                        | L l => inl l
                        | R l => inr (inl l)
                        | LR l1 l2 => inr (inr (l1, l2))
                        end)
                 (λ rl, match rl with
                        | inl l => Some (L l)
                        | inr (inl l) => Some (R l)
                        | inr (inr (l1, l2)) => Some (LR l1 l2)
                        end));
by case.
Qed.

Definition prod_of_matching xy :=
  match xy with
  | L x => (Some x, None)
  | R y => (None, Some y)
  | LR x y => (Some x, Some y)
  end.

Definition part_perm (X : gset matching) :=
  ∀ xy1 xy2 x y1 y2 b,
    xy1 ∈ X →
    xy2 ∈ X →
    prod_of_matching xy1 = flipb b pair (Some x) y1 →
    prod_of_matching xy2 = flipb b pair (Some x) y2 →
    y1 = y2.

End Matching.

Arguments matching T : clear implicits.
Arguments matchingO T : clear implicits.

Definition symbolN := nroot.@"symbol".

Definition symbol_store := gsetUR (matchingO locO).

Class symbolSG Σ := SymbolSG {
  symbol_inG :> inG Σ (authR symbol_store);
}.

Section Symbol.

Context `{!heapG Σ, !cfgSG Σ, !symbolSG Σ}.
Variable γ : gname.

Implicit Types rl : matchingO loc.
Implicit Types l : loc.
Implicit Types RL : symbol_store.
Implicit Types v : val.
Implicit Types b : bool.

Definition symbol_own rl : iProp Σ :=
  match rl with
  | L l => l ↦  #()
  | R l => l ↦ₛ #()
  | LR l1 l2 => l1 ↦ #() ∗ l2 ↦ₛ #()
  end.

Lemma symbol_own_dup rl : symbol_own rl -∗ symbol_own rl -∗ False.
Proof.
case: rl=> [l|l|l1 l2]; iIntros "H1 H2".
- by iPoseProof (mapsto_valid_2 with "H1 H2") as "%Hvalid".
- by iPoseProof (mapstoS_valid_2 with "H1 H2") as "%Hvalid".
- iDestruct "H1" as "[H1 _]"; iDestruct "H2" as "[H2 _]".
  by iPoseProof (mapsto_valid_2 with "H1 H2") as "%Hvalid".
Qed.

Global Instance timeless_symbol_own rl : Timeless (symbol_own rl).
Proof. by case: rl=> *; apply _. Qed.

Definition symbol_inv : iProp Σ := ∃ RL,
  own γ (● RL) ∗ [∗ set] rl ∈ RL, symbol_own rl.
Global Instance timeless_symbol_inv : Timeless symbol_inv.
Proof. apply _. Qed.
Definition symbol_ctx : iProp Σ :=
  inv (symbolN.@γ) symbol_inv.

Definition symbol rl := own γ (◯ {[rl]}).
Global Instance persistent_symbol rl : Persistent (symbol rl).
Proof. apply _. Qed.
Global Instance timeless_symbol rl : Timeless (symbol rl).
Proof. apply _. Qed.

Definition symbol1 b l :=
  symbol ((if b then L else R) l).
Global Instance persistent_symbol1 b l : Persistent (symbol1 b l).
Proof. apply _. Qed.
Global Instance timeless_symbol1 b l : Timeless (symbol1 b l).
Proof. apply _. Qed.

Definition symbol12 b l : iProp Σ :=
  let i1 := if b then L  else R in
  let i2 := flipb b LR in
  symbol (i1 l) ∨ ∃ l', symbol (i2 l l').
Global Instance persistent_symbol12 b l : Persistent (symbol12 b l).
Proof. apply _. Qed.
Global Instance timeless_symbol12 b l : Timeless (symbol12 b l).
Proof. apply _. Qed.

Lemma symbol12_mapsto b l :
  symbol_inv -∗
  symbol12 b l -∗
  if b then l ↦ #() else l ↦ₛ #().
Proof.
iDestruct 1 as (RL) "[Hown Hsymb]".
iDestruct 1 as "[H|H]".
- iPoseProof (own_valid_2 with "Hown H") as "%H".
  rewrite auth_both_valid gset_included -elem_of_subseteq_singleton in H *.
  case=> H _.
  rewrite (big_sepS_delete _ _ _ H).
  iDestruct "Hsymb" as "[Hsymb _]".
  by rewrite /symbol_own; case: (b).
- iDestruct "H" as (l') "H".
  iPoseProof (own_valid_2 with "Hown H") as "%H".
  rewrite auth_both_valid gset_included -elem_of_subseteq_singleton in H *.
  case=> H _.
  rewrite (big_sepS_delete _ _ _ H).
  iDestruct "Hsymb" as "[Hsymb _]".
  by case: (b); iDestruct "Hsymb" as "[??]".
Qed.

Lemma symbol_eq_iff l11 l12 l21 l22 :
  symbol_inv -∗
  symbol (LR l11 l12) -∗
  symbol (LR l21 l22) -∗
  ⌜l11 = l21 ↔ l12 = l22⌝.
Proof.
iDestruct 1 as (RL) "[Hown Halloc]".
rewrite /symbol; iIntros "Hown1 Hown2".
iCombine "Hown1 Hown2" as "Hown'".
iPoseProof (own_valid_2 with "Hown Hown'") as "%Hvalid".
rewrite auth_both_valid gset_op_union gset_included in Hvalid *.
case=> Hsub _.
iPoseProof (big_sepS_subseteq _ _ _ Hsub with "Halloc") as "Halloc".
case: (decide (l11 = l21))=> [e1|ne1];
case: (decide (l12 = l22))=> [e2|ne2].
- iPureIntro; split; move=> *; congruence.
- rewrite big_sepS_insert ?elem_of_singleton; try congruence.
  rewrite big_sepS_singleton /=.
  iDestruct "Halloc" as "[[H1 _] [H2 _]]"; rewrite e1.
  by iPoseProof (mapsto_valid_2 with "H1 H2") as "%contra".
- rewrite big_sepS_insert ?elem_of_singleton; try congruence.
  rewrite big_sepS_singleton /=.
  iDestruct "Halloc" as "[[_ H1] [_ H2]]"; rewrite e2.
  by iPoseProof (mapstoS_valid_2 with "H1 H2") as "%contra".
- iPureIntro; split; move=> *; congruence.
Qed.

Lemma symbol_eqR l1 l21 l22 :
  symbol_inv -∗ symbol (LR l1 l21) -∗ symbol (LR l1 l22) -∗ ⌜l21 = l22⌝.
Proof.
iIntros "Hinv Hown1 Hown2".
iPoseProof (symbol_eq_iff with "Hinv Hown1 Hown2") as "%Hperm".
iPureIntro; exact/Hperm.
Qed.

Lemma symbol_eqL l11 l12 l2 :
  symbol_inv -∗ symbol (LR l11 l2) -∗ symbol (LR l12 l2) -∗ ⌜l11 = l12⌝.
Proof.
iIntros "Hinv Hown1 Hown2".
iPoseProof (symbol_eq_iff with "Hinv Hown1 Hown2") as "%Hperm".
iPureIntro; exact/Hperm.
Qed.

Lemma flipb_symbol_perm b l1 l21 l22 :
  symbol_inv -∗
  symbol (flipb b LR l1 l21) -∗
  symbol (flipb b LR l1 l22) -∗
  ⌜l21 = l22⌝.
Proof.
rewrite /flipb; case: b=> /=.
- exact: symbol_eqR.
- exact: symbol_eqL.
Qed.

End Symbol.

Section Allocation.

Context `{!heapG Σ, !cfgSG Σ, !symbolSG Σ}.

Implicit Types l : loc.
Implicit Types rl : matching loc.
Implicit Types RL : gset (matching loc).
Implicit Types G : list gname.
Implicit Types E : coPset.

Definition mksymbol : val := λ: <>, ref #().

Definition symbols_inv G : iProp Σ :=
  [∗ list] γ ∈ G, symbol_inv γ.
Definition symbols_ctx G : iProp Σ :=
  [∗ list] γ ∈ G, symbol_ctx γ.
Definition symbols G RL : iProp Σ :=
  ∀ rl, ⌜rl ∈ RL⌝ -∗ ∃ γ, ⌜γ ∈ G⌝ ∗ symbol γ rl.

Global Instance timeless_symbols_inv G :
  Timeless (symbols_inv G).
Proof. apply _. Qed.

Global Instance persistent_symbols_ctx G :
  Persistent (symbols_ctx G).
Proof. apply _. Qed.

Global Instance persistent_symbols G RL :
  Persistent (symbols G RL).
Proof. apply _. Qed.

Lemma relinquish  E G γ RL rl :
  ↑symbolN ⊆ E →
  γ ∈ G →
  symbols_ctx G -∗
  symbols G RL -∗
  symbol_own rl ={E}=∗
  symbol γ rl ∗ ⌜rl ∉ RL⌝.
Proof.
move=> HE γ_G; iIntros "#HG #G_RL Hrl".
case: (decide (rl ∈ RL))=> rl_RL.
  iDestruct ("G_RL" $! _ rl_RL) as (γ') "[%Hγ' γ'_rl]".
  iPoseProof (big_sepL_elem_of _ _ _ Hγ' with "HG") as "{HG} HG".
  iInv "HG" as "> Hγ'".
  iDestruct "Hγ'" as (RL') "[Hown Hsymbols]".
  iAssert ⌜rl ∈ RL'⌝%I as "%Hr".
    iPoseProof (own_valid_2 with "Hown γ'_rl") as "%Hin".
    move: Hin.
    rewrite auth_both_valid gset_included elem_of_subseteq_singleton.
    by case.
  rewrite big_sepS_delete; eauto.
  iDestruct "Hsymbols" as "[Hsymbols _]".
  iDestruct (symbol_own_dup with "Hrl Hsymbols") as "[]".
iPoseProof (big_sepL_elem_of _ _ _ γ_G with "HG") as "{HG} HG".
iInv "HG" as "> Hγ".
iDestruct "Hγ" as (RL') "[Hown Hsymbols]".
iMod (own_update _ _ (_ ⋅ (◯ ({[rl]} ⋅ RL'))) with "Hown") as "[Hown Hfrag]".
  by apply auth_update_alloc, gset_local_update, union_subseteq_r.
iDestruct "Hfrag" as "[Hfrag _]".
iModIntro; iSplitL "Hown Hsymbols Hrl".
  iModIntro; iExists ({[rl]} ⋅ RL'); iFrame.
  iAssert ⌜rl ∉ RL'⌝%I with "[Hsymbols Hrl]" as "%rl_RL'".
    iIntros (rl_RL'); rewrite big_sepS_delete //.
    iDestruct "Hsymbols" as "[Hrl' _]".
    iApply (symbol_own_dup with "Hrl Hrl'").
  by rewrite gset_op_union big_sepS_insert //; iFrame.
by iModIntro; iFrame.
Qed.

Lemma step_mksymbol_fresh E j K RL G γ :
  ↑specN ⊆ E →
  ↑symbolN ⊆ E →
  γ ∈ G →
  spec_ctx -∗
  symbols_ctx G -∗
  symbols G RL -∗
  j ⤇ fill K (mksymbol #()%V)
  ={E}=∗ ∃ l, j ⤇ fill K #l ∗ symbol γ (R l) ∗ ⌜R l ∉ RL⌝.
Proof.
iIntros (HE1 HE2 γ_G) "#Hinv #HG #HRL Hspec".
iMod (step_lam E with "[Hinv Hspec]") as "Hspec"; first done.
  by iSplit.
rewrite /=.
iMod (step_alloc E with "[Hinv Hspec]") as (l) "[Hspec Hl]"; first done.
  by iSplit.
iAssert (symbol_own (R l)) with "Hl" as "Hl".
by iMod (relinquish with "HG HRL Hl") as "[??]"; eauto.
Qed.

Lemma wp_mksymbol γ E RL G :
  ↑symbolN ⊆ E →
  γ ∈ G →
  symbols_ctx G -∗
  symbols G RL -∗
  WP mksymbol #()%V @ E {{ v, ∃ l, ⌜v = #l⌝ ∗ symbol γ (L l) ∗ ⌜L l ∉ RL⌝}}.
Proof.
rewrite /symbol_inv /mksymbol.
iIntros (HE γ_G) "#Hinv #Hsymbols".
iApply wp_fupd; wp_alloc l as "Hl".
iAssert (symbol_own (L l)) with "Hl" as "Hl".
by iMod (relinquish with "Hinv Hsymbols Hl"); eauto.
Qed.

Lemma wp_mksymbol2 γ E j K G RL :
  ↑specN ⊆ E →
  ↑symbolN ⊆ E →
  γ ∈ G →
  spec_ctx -∗
  symbols_ctx G -∗
  symbols G RL -∗
  j ⤇ fill K (mksymbol #()%V) -∗
  WP mksymbol #()%V @ E {{ v1, ∃ l1 l2,
    ⌜v1 = #l1⌝ ∗ j ⤇ fill K #l2 ∗ symbol γ (LR l1 l2) ∗ ⌜LR l1 l2 ∉ RL⌝}}.
Proof.
rewrite /symbol_inv /mksymbol => HE1 HE2 γ_G.
iIntros "#Hinv1 #Hinv2 #Hsymbols Hspec".
iApply wp_fupd; wp_alloc l1 as "Hl1".
iMod (step_lam E with "[Hinv1 Hspec]") as "Hspec"=> //.
  by iFrame.
rewrite /=.
iMod (step_alloc E with "[Hinv1 Hspec]") as "Hspec"=> //.
  by iFrame.
iDestruct "Hspec" as (l2) "[Hspec Hl2]".
iAssert (symbol_own (LR l1 l2)) with "[Hl1 Hl2]" as "Hl"; first by iFrame.
iMod (relinquish with "Hinv2 Hsymbols Hl") as "[??]"; eauto.
by iModIntro; iExists l1, l2; iFrame.
Qed.

Lemma symbol_inv_alloc : ⊢ |==> ∃ γ, symbol_inv γ.
Proof.
iMod (own_alloc (● ∅ : auth symbol_store)) as (γ) "Hown".
  by apply/auth_auth_valid.
by iModIntro; iExists γ, ∅; simpl; iFrame.
Qed.

Lemma symbol_disj γ1 γ2 b l :
  symbol_inv γ1 -∗
  symbol_inv γ2 -∗
  symbol12 γ1 b l -∗
  symbol12 γ2 b l -∗
  False.
Proof.
iIntros "Hinv1 Hinv2 Hsymb1 Hsymb2".
iPoseProof (symbol12_mapsto with "Hinv1 Hsymb1") as "H1".
iPoseProof (symbol12_mapsto with "Hinv2 Hsymb2") as "H2".
case: b.
- by iPoseProof (mapsto_valid_2 with "H1 H2") as "%H".
- by iPoseProof (mapstoS_valid_2 with "H1 H2") as "%H".
Qed.

End Allocation.
