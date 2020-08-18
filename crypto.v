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
From crypto Require Import lib basic symbols.

Section Terms.

Context `{heapG Σ, cfgSG Σ, symbolSG Σ}.

Inductive term  :=
| TInt of Z
| TPair of term & term
| TNonce of loc
| TKey of loc
| TEnc of loc & term.

Canonical termO := leibnizO term.

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

Fixpoint term_of_val v : term :=
  match v with
  | PairV (# (LitInt 0)) (# (LitInt n)) =>
    TInt n
  | PairV (# (LitInt 1)) (PairV v1 v2) =>
    TPair (term_of_val v1) (term_of_val v2)
  | PairV (# (LitInt 2)) (# (LitLoc l)) =>
    TNonce l
  | PairV (# (LitInt 3)) (# (LitLoc l)) =>
    TKey l
  | PairV (# (LitInt 4)) (PairV (# (LitLoc l)) v) =>
    TEnc l (term_of_val v)
  | _ => TInt 0
  end.

Global Instance val_of_termK : Cancel (=) term_of_val val_of_term.
Proof. elim=> //= *; congruence. Qed.

Global Instance val_of_term_inj : Inj (=) (=) val_of_term.
Proof.
by apply (@cancel_inj _ _ _ term_of_val); apply _.
Qed.

Global Instance countable_term : Countable term.
Proof. apply (inj_countable' _ _ val_of_termK). Qed.

Class termSG := TermSG {
  term_inG :> inG Σ (authR (gsetUR (matchingO termO)));
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
  symbol12 lo_key_name s l ∨
  symbol12 hi_key_name s l.
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
Definition opaque s t : iProp Σ :=
  match t with
  | TInt _ => False%I
  | TPair _ _ => False%I
  | TNonce l => symbol1 lo_nonce_name s l
  | TKey l => False%I
  | TEnc l t => symbol12 hi_key_name s l ∗ wf_term s t
  end.

Global Instance persistent_opaque s t : Persistent (opaque s t).
Proof. elim: t=> /=; apply _. Qed.

Lemma opaque_wf_term s t : opaque s t -∗ wf_term s t.
Proof.
case: t=> /=.
- by iIntros (_) "?".
- by iIntros (??) "?".
- by iIntros (?) "?"; iLeft.
- by iIntros (?) "?".
- by iIntros (??) "[??]"; iFrame.
Qed.

Fixpoint lo_term1 s t : iProp Σ :=
  match t with
  | TInt _ => True%I
  | TPair t1 t2 => lo_term1 s t1 ∗ lo_term1 s t2
  | TNonce l => symbol1 lo_nonce_name s l
  | TKey l => symbol1 lo_key_name s l
  | TEnc l t => symbol12 lo_key_name s l ∗ lo_term1 s t ∨
                symbol12 hi_key_name s l ∗ wf_term s t
  end.

Lemma persistent_lo_term1 s t : Persistent (lo_term1 s t).
Proof. elim: t=> *; apply _. Qed.

Lemma lo_term1_wf_term1 s t : lo_term1 s t -∗ wf_term s t.
Proof.
elim: t=> [n|t1 IH1 t2 IH2|l|l|l t IH] //=.
- by rewrite IH1 IH2.
- rewrite /wf_nonce; eauto.
- rewrite /wf_key /symbol12; eauto.
- rewrite /wf_key /symbol12; iDestruct 1 as "[[??]|[??]]"; eauto.
  by rewrite IH; iFrame.
Qed.

Lemma opaque_lo_term1 s t : opaque s t -∗ lo_term1 s t.
Proof.
elim: t=> [n|t1 IH1 t2 IH2|l|l|l t IH] //=;
do 1? by iDestruct 1 as "[]".
eauto.
Qed.

Implicit Types TT : gsetUR (matchingO termO).

Definition term_names :=
  [lo_nonce_name; hi_nonce_name; lo_key_name; hi_key_name].

Definition published_inv : iProp Σ :=
  ∃ TT, ([∗ list] γ ∈ term_names, symbol_inv γ)
        ∗ own term_name (● TT)
        ∗ ⌜part_perm TT⌝
        ∗ (∀ tt t1 pt2 b,
             ⌜tt ∈ TT⌝ -∗
             ⌜prod_of_matching tt = flipb b pair (Some t1) pt2⌝ -∗
             opaque b t1).

Definition published tt : iProp Σ :=
  own term_name (◯ {[tt]}).

Definition published1 (s : bool) t :=
  published ((if s then L else R) t).

Global Instance persistent_published tt : Persistent (published tt).
Proof. apply _. Qed.

Lemma published_opaque t1 t2 :
  published_inv -∗
  published (LR t1 t2) -∗
  opaque true t1 ∗ opaque false t2.
Proof.
iDestruct 1 as (TT) "(Hsymb & Hown & %Hperm & #HTT)"; iIntros "#Ht1t2".
iPoseProof (own_valid_2 with "Hown Ht1t2") as "%Hvalid".
move: Hvalid; rewrite auth_both_valid gset_included.
rewrite -elem_of_subseteq_singleton; case=> Ht1t2 _.
iPoseProof ("HTT" $! _ t1 (Some t2) true Ht1t2 eq_refl) as "#H1".
iPoseProof ("HTT" $! _ t2 (Some t1) false Ht1t2 eq_refl) as "#H2".
by iSplit.
Qed.

Lemma published_opaqueL t1 t2:
  published_inv -∗
  published (LR t1 t2) -∗
  opaque true t1.
Proof.
iIntros "Hinv Ht1t2".
by iDestruct (published_opaque with "Hinv Ht1t2") as "[? _]".
Qed.

Lemma published_opaqueR t1 t2 :
  published_inv -∗
  published (LR t1 t2) -∗
  opaque false t2.
Proof.
iIntros "Hinv Ht1t2".
by iDestruct (published_opaque with "Hinv Ht1t2") as "[_ ?]".
Qed.

Fixpoint lo_term_aux t1 t2 : iProp Σ :=
  published (LR t1 t2) ∨
  match t1, t2 with
  | TInt n1, TInt n2 => ⌜n1 = n2⌝
  | TPair t11 t12, TPair t21 t22 =>
    lo_term_aux t11 t21 ∗ lo_term_aux t12 t22
  | TNonce l1, TNonce l2 => False%I (* Nonces are covered by the opaque case
    above *)
  | TKey l1, TKey l2 =>
    symbol lo_key_name (LR l1 l2)
  | TEnc l1 t1, TEnc l2 t2 =>
    symbol lo_key_name (LR l1 l2) ∗ lo_term_aux t1 t2
  | _, _ => False%I
  end.

Definition lo_term_aux_rec t1 t2 : iProp Σ :=
  match t1, t2 with
  | TInt n1, TInt n2 => ⌜n1 = n2⌝
  | TPair t11 t12, TPair t21 t22 =>
    lo_term_aux t11 t21 ∗ lo_term_aux t12 t22
  | TNonce l1, TNonce l2 => False%I
  | TKey l1, TKey l2 =>
    symbol lo_key_name (LR l1 l2)
  | TEnc l1 t1, TEnc l2 t2 =>
    symbol lo_key_name (LR l1 l2) ∗ lo_term_aux t1 t2
  | _, _ => False%I
  end.

Lemma lo_term_auxE t1 t2 :
  lo_term_aux t1 t2 =
  (published (LR t1 t2) ∨ lo_term_aux_rec t1 t2)%I.
Proof. by case: t1. Qed.

Global Instance persistent_lo_term_aux t1 t2 : Persistent (lo_term_aux t1 t2).
Proof.
elim: t1 t2=> /=.
- by move=> ?; case=> *; apply _.
- by move=> ????; case=> *; apply _.
- by move=> ?; case=> *; apply _.
- by move=> ?; case=> *; apply _.
- by move=> ???; case=> *; apply _.
Qed.

Lemma flipb_lo_termE b t1 t2 :
  flipb b lo_term_aux t1 t2 ⊣⊢
  (published (flipb b LR t1 t2) ∨
   match t1, t2 with
   | TInt n1, TInt n2 => ⌜n1 = n2⌝
   | TPair t11 t12, TPair t21 t22 =>
     flipb b lo_term_aux t11 t21 ∗ flipb b lo_term_aux t12 t22
   | TNonce l1, TNonce l2 => False%I
   | TKey l1, TKey l2 =>
     symbol lo_key_name (flipb b LR l1 l2)
   | TEnc l1 t1, TEnc l2 t2 =>
    symbol lo_key_name (flipb b LR l1 l2) ∗ flipb b lo_term_aux t1 t2
  | _, _ => False%I
  end)%I.
Proof.
rewrite /flipb lo_term_auxE.
case: b=> //; iSplit.
- iDestruct 1 as "[H|H]"; eauto; iRight.
  case: t1=> // *; case: t2=> //= *.
  by iDestruct "H" as "->".
- iDestruct 1 as "[H|H]"; eauto; iRight.
  case: t1=> // *; case: t2=> //= *.
  by iDestruct "H" as "->".
Qed.

Lemma flipb_published_perm b t1 t21 t22 :
  published_inv -∗
  published (flipb b LR t1 t21) -∗
  published (flipb b LR t1 t22) -∗
  ⌜t21 = t22⌝.
Proof.
iDestruct 1 as (TT) "(_ & Hown & %Hperm & #HTT)".
rewrite /flipb /opaque; case: b=> /=.
- iIntros "Hown1 Hown2".
  iPoseProof (own_valid_2 with "Hown Hown1") as "%Hval1".
  iPoseProof (own_valid_2 with "Hown Hown2") as "%Hval2".
  move: Hval1; rewrite auth_both_valid gset_included; case=> Hval1 _.
  move: Hval2; rewrite auth_both_valid gset_included; case=> Hval2 _.
  move: Hval1 Hval2; rewrite -!elem_of_subseteq_singleton=> Hval1 Hval2.
  iPureIntro; by case: (Hperm _ _ _ _ _ true Hval1 Hval2 eq_refl eq_refl).
- iIntros "Hown1 Hown2".
  iPoseProof (own_valid_2 with "Hown Hown1") as "%Hval1".
  iPoseProof (own_valid_2 with "Hown Hown2") as "%Hval2".
  move: Hval1; rewrite auth_both_valid gset_included; case=> Hval1 _.
  move: Hval2; rewrite auth_both_valid gset_included; case=> Hval2 _.
  move: Hval1 Hval2; rewrite -!elem_of_subseteq_singleton=> Hval1 Hval2.
  iPureIntro; by case: (Hperm _ _ _ _ _ false Hval1 Hval2 eq_refl eq_refl).
Qed.

Lemma flipb_published_opaque b t1 t2 :
  published_inv -∗
  published (flipb b LR t1 t2) -∗
  opaque b t1.
Proof.
rewrite /flipb; case: b=> /=.
- exact: published_opaqueL.
- exact: published_opaqueR.
Qed.

Lemma flipb_lo_term_aux_perm b t1 t21 t22 :
  published_inv -∗
  flipb b lo_term_aux t1 t21 -∗
  flipb b lo_term_aux t1 t22 -∗
  ⌜t21 = t22⌝.
Proof.
elim: t1 t21 t22.
- move=> n1 t21 t22; iIntros "Hinv #H1 #H2".
  rewrite !flipb_lo_termE.
  iDestruct "H1" as "[H1|H1]".
    by iDestruct (flipb_published_opaque with "Hinv H1") as "[]".
  iDestruct "H2" as "[H2|H2]".
    by iDestruct (flipb_published_opaque with "Hinv H2") as "[]".
  case: t21=> // ?; iDestruct "H1" as "<-".
  by case: t22=> // ?; iDestruct "H2" as "<-".
- move=> t11 IH1 t12 IH2 t21 t22; iIntros "Hinv #H1 #H2".
  rewrite !flipb_lo_termE.
  iDestruct "H1" as "[H1|H1]".
    by iDestruct (flipb_published_opaque with "Hinv H1") as "[]".
  iDestruct "H2" as "[H2|H2]".
    by iDestruct (flipb_published_opaque with "Hinv H2") as "[]".
  case: t21=> //= t211 t212; iDestruct "H1" as "[H11 H12]".
  case: t22=> //= t221 t222; iDestruct "H2" as "[H21 H22]".
  iDestruct (IH1 with "Hinv H11 H21") as "%".
  iDestruct (IH2 with "Hinv H12 H22") as "%".
  iPureIntro; congruence.
- move=> l t21 t22; iIntros "Hinv #H1 #H2".
  rewrite !flipb_lo_termE /=.
  iDestruct "H1" as "[H1|H1]"; last by case: t21.
  iDestruct "H2" as "[H2|H2]"; last by case: t22.
  iPoseProof (flipb_published_perm with "Hinv H1 H2") as "%E".
  by iPureIntro.
- move=> l t21 t22; iIntros "Hinv #H1 #H2".
  rewrite !flipb_lo_termE /=.
  iDestruct "H1" as "[H1|H1]".
    by iDestruct (flipb_published_opaque with "Hinv H1") as "[]".
  iDestruct "H2" as "[H2|H2]".
    by iDestruct (flipb_published_opaque with "Hinv H2") as "[]".
  case: t21=> //= l21; case: t22=> //= l22.
  iDestruct "Hinv" as (?) "[Hsymb _]".
  rewrite !(big_sepL_singleton, big_sepL_cons).
  iDestruct "Hsymb" as "(_ & _ & Hlo_key & _)".
  iPoseProof (flipb_symbol_perm with "Hlo_key H1 H2") as "%E".
  by rewrite E.
- move=> l1 t1 IH t21 t22; iIntros "Hinv #H1 #H2".
  rewrite !flipb_lo_termE.
  iDestruct "H1" as "[H1|H1]"; iDestruct "H2" as "[H2|H2]".
  + iPoseProof (flipb_published_perm with "Hinv H1 H2") as "%E".
    by iPureIntro.
  + case: t22=> //= l22 t22; iDestruct "H2" as "[H2 _]".
    iPoseProof (flipb_published_opaque with "Hinv H1") as "#H1' /=".
    iDestruct "H1'" as "[H1' _]".
    iAssert (symbol12 lo_key_name b l1) as "H2'".
      by iRight; iExists l22.
    iDestruct "Hinv" as (TT) "[Hsymb _]".
    rewrite !(big_sepL_singleton, big_sepL_cons).
    iDestruct "Hsymb" as "(_ & _ & Hlo_key & Hhi_key)".
    by iDestruct (symbol_disj with "Hhi_key Hlo_key H1' H2'") as "[]".
  + case: t21=> //= l21 t21; iDestruct "H1" as "[H1 _]".
    iPoseProof (flipb_published_opaque with "Hinv H2") as "#H2' /=".
    iDestruct "H2'" as "[H2' _]".
    iAssert (symbol12 lo_key_name b l1) as "H1'".
      by iRight; iExists l21.
    iDestruct "Hinv" as (TT) "[Hsymb _]".
    rewrite !(big_sepL_singleton, big_sepL_cons).
    iDestruct "Hsymb" as "(_ & _ & Hlo_key & Hhi_key)".
    by iDestruct (symbol_disj with "Hhi_key Hlo_key H2' H1'") as "[]".
  + case: t21 t22=> //= l21 t21 [] //= l22 t22.
    iDestruct "H1" as "[Hl21 Ht21]".
    iDestruct "H2" as "[Hl22 Ht22]".
    iPoseProof (IH with "Hinv Ht21 Ht22") as "%Et".
    iDestruct "Hinv" as (TT) "[Hsymb _]".
    rewrite !(big_sepL_singleton, big_sepL_cons).
    iDestruct "Hsymb" as "(? & ? & Hlo_key & ?)".
    iPoseProof (flipb_symbol_perm with "Hlo_key Hl21 Hl22") as "%El".
    iPureIntro; congruence.
Qed.

Lemma lo_term_aux_perm t11 t12 t21 t22 :
  published_inv -∗
  lo_term_aux t11 t12 -∗
  lo_term_aux t21 t22 -∗
  ⌜t11 = t21 ↔ t12 = t22⌝.
Proof.
iIntros "Hinv #H1 #H2"; rewrite /iff; iSplit.
- iIntros (E); rewrite -{}E.
  by iApply (@flipb_lo_term_aux_perm true with "Hinv H1 H2").
- iIntros (E); rewrite -{}E.
  by iApply (@flipb_lo_term_aux_perm false with "Hinv H1 H2").
Qed.

Implicit Types T : gset term.

Fixpoint symbols_of_term t : gset loc :=
  match t with
  | TInt _ => ∅
  | TPair t1 t2 => symbols_of_term t1 ∪ symbols_of_term t2
  | TNonce l => {[l]}
  | TKey l => {[l]}
  | TEnc l t => {[l]} ∪ symbols_of_term t
  end.

(* l does not occur in t, except in occurrences that appear in T. *)
Fixpoint protected_aux l T t :=
  t ∈ T ∨
  match t with
  | TInt _ => True
  | TPair t1 t2 => protected_aux l T t1 ∧ protected_aux l T t2
  | TNonce l' => l ≠ l'
  | TKey l' => l ≠ l'
  | TEnc _ t2 => protected_aux l T t2
  end.

Definition protected s l (T : gset term) : iProp Σ :=
  (∀ t, lo_term1 s t → ⌜protected_aux l T t⌝)%I.

Lemma protected_extend l1 l2 T1 T2 t1 t2 :
  l1 ∈ symbols_of_term t1 →
  l2 ∈ symbols_of_term t2 →
  t1 ∉ T1 →
  t2 ∉ T2 →
  published_inv -∗
  protected true  l1 T1 -∗
  protected false l2 T2 -∗
  opaque true  t1 -∗
  opaque false t2 -∗
  |==> lo_term_aux t1 t2.
Proof. Admitted.

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

Lemma step_eq_term t1 t2 :
  ⊢ swp (eq_term (val_of_term t1) (val_of_term t2))
        (λ v, ⌜v = #(bool_decide (t1 = t2))⌝)%I.
Proof.
elim: t1 t2=> [n1|t11 IH1 t12 IH2|l1|l1|l1 t1 IH1];
case=> [n2|t21 t22|l2|l2|l2 t2] /=;
swp_rec; swp_pures=> //.
- iPureIntro; congr (# (LitBool _)).
  apply: bool_decide_iff; intuition congruence.
- swp_bind (eq_term _ _).
  iPoseProof (IH1 t21) as "IH1"; iPoseProof (IH2 t22) as "IH2".
  iApply (swp_wand with "IH1"); iIntros (?) "->".
  case: bool_decide_reflect=> e1.
  + swp_pures; iApply (swp_wand with "IH2"); iIntros (?) "->".
    iPureIntro; congr (# (LitBool _)).
    apply: bool_decide_iff; intuition congruence.
  + swp_pures; iPureIntro; congr (# (LitBool _)).
    rewrite bool_decide_false; congruence.
- iPureIntro; congr (# (LitBool _)).
  apply: bool_decide_iff; intuition congruence.
- iPureIntro; congr (# (LitBool _)).
  apply: bool_decide_iff; intuition congruence.
- case: bool_decide_reflect=> e1.
  + swp_pures.
    iPoseProof (IH1 t2) as "IH1".
    iApply (swp_wand with "IH1"); iIntros (?) "->".
    iPureIntro; congr (# (LitBool _)).
    apply: bool_decide_iff; intuition congruence.
  + swp_pures; iPureIntro; congr (# (LitBool _)).
    rewrite bool_decide_false; congruence.
Qed.

Lemma swp_elim E e Φ j K :
  nclose specN ⊆ E →
  swp e Φ -∗
  spec_ctx -∗
  j ⤇ fill K e ={E}=∗
  ∃ v : val, j ⤇ fill K v ∗ Φ v.
Proof.
rewrite swp_eq; move=> HE; iIntros "Hswp Hspec Hj".
iCombine "Hspec Hj" as "Hspec".
by iApply "Hswp".
Qed.

Lemma wp_eq_term2 v11 v12 v21 v22 j K :
  lo_term v11 v12 -∗
  lo_term v21 v22 -∗
  published_inv -∗
  spec_ctx -∗
  j ⤇ fill K (eq_term v12 v22) -∗
  WP eq_term v11 v21
     {{ v, ⌜v = #(bool_decide (v11 = v21))⌝ ∗ j ⤇ fill K v }}.
Proof.
iDestruct 1 as (t11 t12) "(-> & -> & #Ht1)".
iDestruct 1 as (t21 t22) "(-> & -> & #Ht2)".
iIntros "Hopaque Hspec Hj"; iApply fupd_wp.
iPoseProof (step_eq_term t12 t22) as "Hswp".
iMod (swp_elim with "Hswp Hspec Hj") as (v) "[Hj ->]"; first done.
iModIntro; iPoseProof (wp_eq_term t11 t21) as "Hwp".
iApply (wp_wand with "Hwp"); iIntros (v) "->".
iAssert ⌜bool_decide (t12 = t22) = bool_decide (t11 = t21)⌝%I
        with "[Hopaque]" as "->".
  iPoseProof (lo_term_aux_perm with "Hopaque Ht1 Ht2") as "%HE".
  by iPureIntro; apply: bool_decide_iff.
iFrame; iPureIntro; congr (# (LitBool _)).
apply: bool_decide_iff; split; try congruence.
apply: val_of_term_inj.
Qed.

End Terms.
