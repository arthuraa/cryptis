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
Import uPred.

Definition perm `{!EqDecision T, !Countable T} (X : gset (T * T)) :=
  forall p1 p2, p1 ∈ X → p2 ∈ X → (p1.1 = p2.1 ↔ p1.2 = p2.2).

Inductive rloc := L of loc | R of loc | LR of loc & loc.
Canonical rlocO := leibnizO rloc.

Instance rloc_dec : EqDecision rloc.
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
Qed.

Instance rloc_countable : Countable rloc.
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

Definition symbol_store := gsetUR rlocO.

Class symbolSG Σ := SymbolSG {
  symbol_inG :> inG Σ (authR symbol_store);
}.

Section Symbol.

Context `{!heapG Σ, !cfgSG Σ, symbolSG Σ}.
Variable γ : gname.

Implicit Types rl : rloc.
Implicit Types l : loc.
Implicit Types RL : symbol_store.
Implicit Types v : val.

Definition symbol_own rl : iProp Σ :=
  match rl with
  | L l => l ↦  #()
  | R l => l ↦ₛ #()
  | LR l1 l2 => l1 ↦ #() ∗ l2 ↦ₛ #()
  end.

Definition symbol_inv : iProp Σ := ∃ RL,
  own γ (● RL) ∗ [∗ set] rl ∈ RL, symbol_own rl.

Definition symbol rl := own γ (◯ {[rl]}).

Lemma persistent_symbol rl : Persistent (symbol rl).
Proof. apply _. Qed.

Definition mksymbol : val := λ: <>, ref #().

Lemma step_mksymbol E j K :
  nclose specN ⊆ E →
  spec_ctx -∗
  symbol_inv -∗
  j ⤇ fill K (mksymbol #()%V)
  ={E}=∗ ∃ l, j ⤇ fill K #l ∗ symbol (R l).
Proof.
rewrite /symbol_inv /mksymbol.
iIntros (HE) "#Hinv"; iDestruct 1 as (RL) "[Hown Hlocs]"; iIntros "Hspec".
iMod (step_lam E with "[Hinv Hspec]") as "Hspec"; first done.
  by iSplit.
rewrite /=.
iMod (step_alloc E with "[Hinv Hspec]") as (l) "[Hspec Hl]"; first done.
  by iSplit.
pose (frag := {[R l]} : symbol_store).
iMod (own_update _ _ (_ ⋅ ◯ (RL ⋅ frag)) with "Hown") as "[Hown [_ Hfrag]]".
  by apply auth_update_alloc, gset_local_update, union_subseteq_l.
by iModIntro; iExists l; iFrame.
Qed.

Lemma wp_mksymbol E :
  spec_ctx -∗
  symbol_inv -∗
  WP mksymbol #()%V @ E {{ v, ∃ l, ⌜v = #l⌝ ∗ symbol (L l) }}.
Proof.
rewrite /symbol_inv /mksymbol.
iIntros "#Hinv"; iDestruct 1 as (RL) "[Hown Hlocs]".
iApply wp_fupd; wp_alloc l as "Hl".
pose (frag := {[L l]} : symbol_store).
iMod (own_update _ _ (_ ⋅ ◯ (RL ⋅ frag)) with "Hown") as "[Hown [_ Hfrag]]".
  apply auth_update_alloc, gset_local_update, union_subseteq_l.
by iModIntro; iExists l; iSplit.
Qed.

Lemma wp_mksymbol2 E j K :
  nclose specN ⊆ E →
  spec_ctx -∗
  symbol_inv -∗
  j ⤇ fill K (mksymbol #()%V) -∗
  WP mksymbol #()%V @ E {{ v1, ∃ l1 l2,
    ⌜v1 = #l1⌝ ∗ j ⤇ fill K #l2 ∗ symbol (LR l1 l2) }}.
Proof.
rewrite /symbol_inv /mksymbol => Hclose.
iIntros "#Hinv"; iDestruct 1 as (RL) "[Hown Hlocs]".
iIntros "Hspec".
iApply wp_fupd; wp_alloc l1 as "Hl1".
iMod (step_lam E with "[Hinv Hspec]") as "Hspec"=> //.
  by iFrame.
rewrite /=.
iMod (step_alloc E with "[Hinv Hspec]") as "Hspec"=> //.
  by iFrame.
iDestruct "Hspec" as (l2) "[Hspec Hl2]".
iMod (own_update _ _ (_ ⋅ ◯ (RL ⋅ {[LR l1 l2]})) with "Hown") as "[Hown [_ H]]".
  apply auth_update_alloc, gset_local_update, union_subseteq_l.
by iModIntro; iExists l1, l2; iFrame.
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

End Symbol.

Lemma symbol_inv_alloc `{!heapG Σ, cfgSG Σ, symbolSG Σ} :
  ⊢ |==> ∃ γ, symbol_inv γ.
Proof.
iMod (own_alloc (● ∅ : auth symbol_store)) as (γ) "Hown".
  by apply/auth_auth_valid.
by iModIntro; iExists γ, ∅; simpl; iFrame.
Qed.
