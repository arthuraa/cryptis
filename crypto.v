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
From crypto Require Import lib basic symbols term.

Definition termN := nroot.@"term".

Section Terms.

Context `{heapG Σ, cfgSG Σ, symbolSG Σ}.

Class termSG := TermSG {
  term_inG :> inG Σ (authR (gsetUR (matchingO termO)));
  nonce_inG :> inG Σ (authR (gmapUR (loc * bool) (gsetUR loc)));
  key_inG :> inG Σ (authR (gmapUR (loc * bool) (agreeR (termO -n> iPropO Σ))));
  hi_key_name : gname;
  lo_key_name : gname;
  hi_nonce_name : gname;
  lo_nonce_name : gname;
  term_name : gname;
  nonce_name : gname;
  key_name : gname;
}.

Context `{termSG}.

Definition al_nonce s l : iProp Σ :=
  symbol1 lo_nonce_name s l ∨
  symbol1 hi_nonce_name s l.
Global Instance persistent_al_nonce s l : Persistent (al_nonce s l).
Proof. apply _. Qed.

Definition al_key s l : iProp Σ :=
  symbol12 lo_key_name s l ∨
  symbol12 hi_key_name s l.
Global Instance persistent_al_key s l : Persistent (al_key s l).
Proof. apply _. Qed.

(* Holds iff all the symbols that appear in the term have been allocated. *)
Fixpoint al_term s t : iProp Σ :=
  match t with
  | TInt _ => True%I
  | TPair t1 t2 => al_term s t1 ∗ al_term s t2
  | TNonce l => al_nonce s l
  | TKey l => al_key s l
  | TEnc l t => al_key s l ∗ al_term s t
  end.
Global Instance persistent_al_term s t : Persistent (al_term s t).
Proof. elim: t=> /=; apply _. Qed.
Global Instance timeless_al_term s t : Timeless (al_term s t).
Proof. elim: t=> /=; apply _. Qed.

(* Opaque terms are those that cannot be inspected by the attacker. *)
Definition opaque s t : iProp Σ :=
  match t with
  | TInt _ => False%I
  | TPair _ _ => False%I
  | TNonce l => symbol1 lo_nonce_name s l
  | TKey l => False%I
  | TEnc l t => symbol12 hi_key_name s l ∗ al_term s t
  end.

Global Instance persistent_opaque s t : Persistent (opaque s t).
Proof. elim: t=> /=; apply _. Qed.
Global Instance timeless_opaque s t : Timeless (opaque s t).
Proof. elim: t=> /=; apply _. Qed.

Lemma opaque_al_term s t : opaque s t -∗ al_term s t.
Proof.
case: t=> /=.
- by iIntros (_) "?".
- by iIntros (??) "?".
- by iIntros (?) "?"; iLeft.
- by iIntros (?) "?".
- by iIntros (??) "[??]"; iFrame.
Qed.

Implicit Types TT : gsetUR (matchingO termO).
Implicit Types NM : gmapUR (loc * bool) (gsetUR loc).
Implicit Types KM : gmapUR (loc * bool) (agreeR (termO -n> iPropO Σ)).
Implicit Types E : coPset.
Implicit Types KS : gset loc.
Implicit Types φ : termO -n> iPropO Σ.

Definition term_names :=
  [lo_nonce_name; hi_nonce_name; lo_key_name; hi_key_name].

(** When we create a secret nonce, we must specify which keys can be used to
encrypt it.  The [guarded_nonce l KS t] predicate below holds when every
occurrence of the nonce [l] in [t] appears in a subterm encrypted with one of
the keys in [KS].  The map between nonces and encryption keys, [NM], is stored
in ghost state in the [nonce_inv TT] predicate below.  The predicate ensures
that every published term in [TT] respects [NM]. *)

Fixpoint guarded_nonce l KS t :=
  match t with
  | TInt _ => True
  | TPair t1 t2 => guarded_nonce l KS t1 ∧ guarded_nonce l KS t2
  | TNonce l' => l' ≠ l
  | TKey _ => True
  | TEnc l' t => l' ∈ KS ∨ guarded_nonce l KS t
  end.

Definition nonce_inv TT : iProp Σ :=
  ∃ NM, own nonce_name (● NM)
        ∗ ([∗ map] lb ↦ KS ∈ NM,
           symbol12 hi_nonce_name lb.2 lb.1
           ∗ [∗ set] l ∈ KS, symbol12 hi_key_name lb.2 l)
        ∗ (∀ tt t1 pt2 l b KS,
            ⌜tt ∈ TT⌝ -∗
            ⌜prod_of_matching tt = flipb b pair (Some t1) pt2⌝ -∗
            ⌜NM !! (l, b) = Some KS⌝ -∗
            ⌜guarded_nonce l KS t1⌝).

Global Instance persistent_nonce_inv TT :
  Timeless (nonce_inv TT).
Proof. apply _. Qed.

(** When we create a secret (high) key, we must specify a predicate that must
hold of all the terms encrypted with that key.  *)

Fixpoint correct_enc l φ t : iProp Σ :=
  match t with
  | TInt _ => True
  | TPair t1 t2 => correct_enc l φ t1 ∗ correct_enc l φ t2
  | TNonce _ => True
  | TKey _ => True
  | TEnc l' t' => if decide (l' = l) then φ t' else correct_enc l φ t'
  end.

Definition key_inv TT : iProp Σ :=
  ∃ KM, own key_name (● KM)
        ∗ ([∗ map] lb ↦ _ ∈ KM, symbol12 hi_key_name lb.2 lb.1)
        ∗ (∀ tt t1 pt2 l b φ,
              ⌜tt ∈ TT⌝ -∗
              ⌜prod_of_matching tt = flipb b pair (Some t1) pt2⌝ -∗
              ⌜KM !! (l, b) ≡ Some (to_agree φ)⌝ -∗
              correct_enc l φ t1).

(** Finally, every opaque term must be registered in a set [TT] in order for it
to be considered public.  The set [TT] must be correct with respect to the
invariants imposed on nonces and keys.  The invariant is not necessarily
timeless, since the predicates associated with keys could be arbitrary. *)

Definition term_inv : iProp Σ :=
  ∃ TT,
    own term_name (● TT)
    ∗ nonce_inv TT
    ∗ key_inv TT
    ∗ ⌜part_perm TT⌝
    ∗ (∀ tt t1 pt2 b,
          ⌜tt ∈ TT⌝ -∗
          ⌜prod_of_matching tt = flipb b pair (Some t1) pt2⌝ -∗
          opaque b t1).

Definition term_ctx :=
  inv termN term_inv.

Definition published tt : iProp Σ :=
  own term_name (◯ {[tt]}).

Definition published1 (s : bool) t :=
  published ((if s then L else R) t).

Definition published12 s t : iProp Σ :=
  published1 s t ∨
  (∃ t', published (flipb s LR t t')).

Global Instance persistent_published tt : Persistent (published tt).
Proof. apply _. Qed.

Global Instance persistent_published1 s t : Persistent (published1 s t).
Proof. apply _. Qed.

Global Instance persistent_published12 s t : Persistent (published12 s t).
Proof. apply _. Qed.

Lemma published_opaque b tt t1 pt2 :
  term_inv -∗
  published tt -∗
  ⌜prod_of_matching tt = flipb b pair (Some t1) pt2⌝ -∗
  opaque b t1.
Proof.
iDestruct 1 as (TT) "(Hown & _ & _ & %Hperm & #HTT)".
iIntros "#Ht1t2 #He".
iPoseProof (own_valid_2 with "Hown Ht1t2") as "%Hvalid".
move: Hvalid; rewrite auth_both_valid gset_included.
rewrite -elem_of_subseteq_singleton; case=> Ht1t2 _.
by iPoseProof ("HTT" $! _ t1 pt2 b Ht1t2 with "He") as "#Hopaque".
Qed.

Lemma published1_opaque b t:
  term_inv -∗
  published1 b t -∗
  opaque b t.
Proof.
iIntros "Hinv Ht1t2".
iApply (published_opaque with "Hinv Ht1t2").
iPureIntro; by case: b.
Qed.

Lemma published12_opaque b t :
  term_inv -∗
  published12 b t -∗
  opaque b t.
Proof.
iIntros "Hinv [Ht1t2|Ht1t2]".
  by iApply (published1_opaque with "Hinv").
iDestruct "Ht1t2" as (t') "#Ht1t2".
iApply (published_opaque _ _ _ (Some t') with "Hinv Ht1t2").
by case: b.
Qed.

Fixpoint lo_term1 s t : iProp Σ :=
  published12 s t ∨
  match t with
  | TInt _ => True%I
  | TPair t1 t2 => lo_term1 s t1 ∗ lo_term1 s t2
  | TNonce l => False%I
  | TKey l => symbol12 lo_key_name s l
  | TEnc l t => symbol12 lo_key_name s l ∗ lo_term1 s t
  end.

Global Instance persistent_lo_term1 s t : Persistent (lo_term1 s t).
Proof. elim: t=> *; apply _. Qed.

Lemma lo_term1_al_term s t :
  term_inv -∗
  lo_term1 s t -∗
  al_term s t.
Proof.
elim: t=> [n|t1 IH1 t2 IH2|l|l|l t IH] //=; eauto.
- iIntros "Hinv [H|H]".
    iAssert (opaque s (TPair t1 t2)) with "[Hinv H]" as "?"=> //.
    by iApply (published12_opaque with "Hinv H").
  iDestruct "H" as "[#H1 #H2]".
  iPoseProof (IH1 with "Hinv H1") as "#?".
  iPoseProof (IH2 with "Hinv H2") as "#?".
  by iSplit.
- iIntros "Hinv [H|?] //".
  iPoseProof (published12_opaque with "Hinv H") as "?".
  by iLeft.
- iIntros "Hinv [H|H]".
    by iPoseProof (published12_opaque with "Hinv H") as "?".
  by iLeft.
- iIntros "Hinv [H|[Hl Ht]]".
    iDestruct (published12_opaque with "Hinv H") as "[Hl Ht]".
    by iFrame.
  iFrame; iApply (IH with "Hinv Ht").
Qed.

Fixpoint lo_term_aux t1 t2 : iProp Σ :=
  published (LR t1 t2) ∨
  match t1, t2 with
  | TInt n1, TInt n2 => ⌜n1 = n2⌝
  | TPair t11 t12, TPair t21 t22 =>
    lo_term_aux t11 t21 ∗ lo_term_aux t12 t22
  | TNonce l1, TNonce l2 =>
    (* Nonces are covered by the published case above *)
    False%I
  | TKey l1, TKey l2 =>
    symbol lo_key_name (LR l1 l2)
  | TEnc l1 t1, TEnc l2 t2 =>
    (* Ditto for terms encrypted with a high key *)
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
  term_inv -∗
  published (flipb b LR t1 t21) -∗
  published (flipb b LR t1 t22) -∗
  ⌜t21 = t22⌝.
Proof.
iDestruct 1 as (TT) "(Hown & _ & _ & %Hperm & #HTT)".
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
  term_inv -∗
  published (flipb b LR t1 t2) -∗
  opaque b t1.
Proof.
rewrite /flipb; case: b=> /=.
- by iIntros "Hinv Htt"; iApply (published_opaque with "Hinv Htt").
- by iIntros "Hinv Htt"; iApply (published_opaque with "Hinv Htt").
Qed.

Lemma flipb_lo_term_aux_perm b t1 t21 t22 :
  symbols_inv term_names -∗
  term_inv -∗
  flipb b lo_term_aux t1 t21 -∗
  flipb b lo_term_aux t1 t22 -∗
  ⌜t21 = t22⌝.
Proof.
elim: t1 t21 t22.
- move=> n1 t21 t22; iIntros "Hsymb Hinv #H1 #H2".
  rewrite !flipb_lo_termE.
  iDestruct "H1" as "[H1|H1]".
    by iDestruct (flipb_published_opaque with "Hinv H1") as "[]".
  iDestruct "H2" as "[H2|H2]".
    by iDestruct (flipb_published_opaque with "Hinv H2") as "[]".
  case: t21=> // ?; iDestruct "H1" as "<-".
  by case: t22=> // ?; iDestruct "H2" as "<-".
- move=> t11 IH1 t12 IH2 t21 t22; iIntros "Hsymb Hinv #H1 #H2".
  rewrite !flipb_lo_termE.
  iDestruct "H1" as "[H1|H1]".
    by iDestruct (flipb_published_opaque with "Hinv H1") as "[]".
  iDestruct "H2" as "[H2|H2]".
    by iDestruct (flipb_published_opaque with "Hinv H2") as "[]".
  case: t21=> //= t211 t212; iDestruct "H1" as "[H11 H12]".
  case: t22=> //= t221 t222; iDestruct "H2" as "[H21 H22]".
  iPoseProof (IH1 with "Hsymb Hinv H11 H21") as "%".
  iPoseProof (IH2 with "Hsymb Hinv H12 H22") as "%".
  iPureIntro; congruence.
- move=> l t21 t22; iIntros "Hsymb Hinv #H1 #H2".
  rewrite !flipb_lo_termE /=.
  iDestruct "H1" as "[H1|H1]"; last by case: t21.
  iDestruct "H2" as "[H2|H2]"; last by case: t22.
  iPoseProof (flipb_published_perm with "Hinv H1 H2") as "%".
  by iPureIntro.
- move=> l t21 t22; iIntros "Hsymb Hinv #H1 #H2".
  rewrite !flipb_lo_termE /=.
  iDestruct "H1" as "[H1|H1]".
    by iDestruct (flipb_published_opaque with "Hinv H1") as "[]".
  iDestruct "H2" as "[H2|H2]".
    by iDestruct (flipb_published_opaque with "Hinv H2") as "[]".
  case: t21=> //= l21; case: t22=> //= l22.
  rewrite /symbols_inv !(big_sepL_singleton, big_sepL_cons).
  iDestruct "Hsymb" as "(_ & _ & Hlo_key & _)".
  iPoseProof (flipb_symbol_perm with "Hlo_key H1 H2") as "%E".
  by rewrite E.
- move=> l1 t1 IH t21 t22; iIntros "Hsymb Hinv #H1 #H2".
  rewrite !flipb_lo_termE.
  iDestruct "H1" as "[H1|H1]"; iDestruct "H2" as "[H2|H2]".
  + iPoseProof (flipb_published_perm with "Hinv H1 H2") as "%E".
    by iPureIntro.
  + case: t22=> //= l22 t22; iDestruct "H2" as "[H2 _]".
    iPoseProof (flipb_published_opaque with "Hinv H1") as "#H1' /=".
    iDestruct "H1'" as "[H1' _]".
    iAssert (symbol12 lo_key_name b l1) as "H2'".
      by iRight; iExists l22.
    rewrite /symbols_inv !(big_sepL_singleton, big_sepL_cons).
    iDestruct "Hsymb" as "(_ & _ & Hlo_key & Hhi_key)".
    by iDestruct (symbol_disj with "Hhi_key Hlo_key H1' H2'") as "[]".
  + case: t21=> //= l21 t21; iDestruct "H1" as "[H1 _]".
    iPoseProof (flipb_published_opaque with "Hinv H2") as "#H2' /=".
    iDestruct "H2'" as "[H2' _]".
    iAssert (symbol12 lo_key_name b l1) as "H1'".
      by iRight; iExists l21.
    rewrite /symbols_inv !(big_sepL_singleton, big_sepL_cons).
    iDestruct "Hsymb" as "(_ & _ & Hlo_key & Hhi_key)".
    by iDestruct (symbol_disj with "Hhi_key Hlo_key H2' H1'") as "[]".
  + case: t21 t22=> //= l21 t21 [] //= l22 t22.
    iDestruct "H1" as "[Hl21 Ht21]".
    iDestruct "H2" as "[Hl22 Ht22]".
    iPoseProof (IH with "Hsymb Hinv Ht21 Ht22") as "%Et".
    rewrite /symbols_inv !(big_sepL_singleton, big_sepL_cons).
    iDestruct "Hsymb" as "(? & ? & Hlo_key & ?)".
    iPoseProof (flipb_symbol_perm with "Hlo_key Hl21 Hl22") as "%El".
    iPureIntro; congruence.
Qed.

Lemma lo_term_aux_perm t11 t12 t21 t22 :
  symbols_inv term_names -∗
  term_inv -∗
  lo_term_aux t11 t12 -∗
  lo_term_aux t21 t22 -∗
  ⌜t11 = t21 ↔ t12 = t22⌝.
Proof.
iIntros "Hsymb Hinv #H1 #H2"; rewrite /iff; iSplit.
- iIntros (E); rewrite -{}E.
  by iApply (@flipb_lo_term_aux_perm true with "Hsymb Hinv H1 H2").
- iIntros (E); rewrite -{}E.
  by iApply (@flipb_lo_term_aux_perm false with "Hsymb Hinv H1 H2").
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
  term_inv -∗
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

Definition mknonce : val := (λ: <>, ref #()).

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
  symbols_inv term_names -∗
  term_inv -∗
  spec_ctx -∗
  j ⤇ fill K (eq_term v12 v22) -∗
  WP eq_term v11 v21
     {{ v, ⌜v = #(bool_decide (v11 = v21))⌝ ∗ j ⤇ fill K v }}.
Proof.
iDestruct 1 as (t11 t12) "(-> & -> & #Ht1)".
iDestruct 1 as (t21 t22) "(-> & -> & #Ht2)".
iIntros "Hsymb Hopaque Hspec Hj"; iApply fupd_wp.
iPoseProof (step_eq_term t12 t22) as "Hswp".
iMod (swp_elim with "Hswp Hspec Hj") as (v) "[Hj ->]"; first done.
iModIntro; iPoseProof (wp_eq_term t11 t21) as "Hwp".
iApply (wp_wand with "Hwp"); iIntros (v) "->".
iAssert ⌜bool_decide (t12 = t22) = bool_decide (t11 = t21)⌝%I
        with "[Hsymb Hopaque]" as "->".
  iPoseProof (lo_term_aux_perm with "Hsymb Hopaque Ht1 Ht2") as "%HE".
  by iPureIntro; apply: bool_decide_iff.
iFrame; iPureIntro; congr (# (LitBool _)).
apply: bool_decide_iff; split; try congruence.
apply: val_of_term_inj.
Qed.

End Terms.
