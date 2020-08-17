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
Definition opaque1 s t : iProp Σ :=
  match t with
  | TInt _ => False%I
  | TPair _ _ => False%I
  | TNonce l => symbol1 lo_nonce_name s l
  | TKey l => False%I
  | TEnc l t => symbol12 hi_key_name s l ∗ wf_term s t
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

Definition term_names :=
  [lo_nonce_name; hi_nonce_name; lo_key_name; hi_key_name].

Definition opaque_inv : iProp Σ :=
  ∃ TT, ([∗ list] γ ∈ term_names, symbol_inv γ)
        ∗ own term_name (● TT)
        ∗ ⌜perm TT⌝
        ∗ (∀ v1 v2, ⌜(v1, v2) ∈ TT⌝ -∗
           ∃ t1 t2, ⌜v1 = val_of_term t1⌝ ∗
                    ⌜v2 = val_of_term t2⌝ ∗
                    opaque1 true t1 ∗ opaque1 false t2).

Definition opaque v1 v2 : iProp Σ :=
  own term_name (◯ {[v1, v2]}).

Global Instance persistent_opaque v1 v2 : Persistent (opaque v1 v2).
Proof. apply _. Qed.

Lemma opaque_opaque1 v1 v2 :
  opaque_inv -∗
  opaque v1 v2 -∗
  opaque1 true (term_of_val v1) ∗ opaque1 false (term_of_val v2).
Proof.
iDestruct 1 as (TT) "(Hsymb & Hown & %Hperm & HTT)"; iIntros "#Ht1t2".
iPoseProof (own_valid_2 with "Hown Ht1t2") as "%Hvalid".
move: Hvalid; rewrite auth_both_valid gset_included.
rewrite -elem_of_subseteq_singleton; case=> Ht1t2 _.
iDestruct ("HTT" $! _ _ Ht1t2) as (t1 t2) "(-> & -> & Ht1 & Ht2)".
by rewrite !cancel; iFrame.
Qed.

Lemma opaque_opaque1L v1 v2 :
  opaque_inv -∗
  opaque v1 v2 -∗
  opaque1 true (term_of_val v1).
Proof.
iIntros "Hinv Ht1t2".
by iDestruct (opaque_opaque1 with "Hinv Ht1t2") as "[? _]".
Qed.

Lemma opaque_opaque1R v1 v2 :
  opaque_inv -∗
  opaque v1 v2 -∗
  opaque1 false (term_of_val v2).
Proof.
iIntros "Hinv Ht1t2".
by iDestruct (opaque_opaque1 with "Hinv Ht1t2") as "[_ ?]".
Qed.

Fixpoint lo_term_aux t1 t2 : iProp Σ :=
  opaque (val_of_term t1) (val_of_term t2) ∨
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
  (opaque (val_of_term t1) (val_of_term t2) ∨
   lo_term_aux_rec t1 t2)%I.
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
  (flipb b opaque (val_of_term t1) (val_of_term t2) ∨
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

Lemma flipb_opaque_perm b v1 v21 v22 :
  opaque_inv -∗
  flipb b opaque v1 v21 -∗
  flipb b opaque v1 v22 -∗
  ⌜v21 = v22⌝.
Proof.
iDestruct 1 as (TT) "(_ & Hown & %Hperm & HTT)".
rewrite /flipb /opaque; case: b=> /=.
- iIntros "Hown1 Hown2".
  iPoseProof (own_valid_2 with "Hown Hown1") as "%Hval1".
  iPoseProof (own_valid_2 with "Hown Hown2") as "%Hval2".
  move: Hval1; rewrite auth_both_valid gset_included; case=> Hval1 _.
  move: Hval2; rewrite auth_both_valid gset_included; case=> Hval2 _.
  move: Hval1 Hval2; rewrite -!elem_of_subseteq_singleton=> Hval1 Hval2.
  iPureIntro; by apply (Hperm _ _ Hval1 Hval2).
- iIntros "Hown1 Hown2".
  iPoseProof (own_valid_2 with "Hown Hown1") as "%Hval1".
  iPoseProof (own_valid_2 with "Hown Hown2") as "%Hval2".
  move: Hval1; rewrite auth_both_valid gset_included; case=> Hval1 _.
  move: Hval2; rewrite auth_both_valid gset_included; case=> Hval2 _.
  move: Hval1 Hval2; rewrite -!elem_of_subseteq_singleton=> Hval1 Hval2.
  iPureIntro; by apply (Hperm _ _ Hval1 Hval2).
Qed.

Lemma flipb_opaque_opaque1 b v1 v2 :
  opaque_inv -∗
  flipb b opaque v1 v2 -∗
  opaque1 b (term_of_val v1).
Proof.
rewrite /flipb; case: b=> /=.
- exact: opaque_opaque1L.
- exact: opaque_opaque1R.
Qed.

Lemma flipb_lo_term_aux_perm b t1 t21 t22 :
  opaque_inv -∗
  flipb b lo_term_aux t1 t21 -∗
  flipb b lo_term_aux t1 t22 -∗
  ⌜t21 = t22⌝.
Proof.
elim: t1 t21 t22.
- move=> n1 t21 t22; iIntros "Hinv #H1 #H2".
  rewrite !flipb_lo_termE.
  iDestruct "H1" as "[H1|H1]".
    by iDestruct (flipb_opaque_opaque1 with "Hinv H1") as "[]".
  iDestruct "H2" as "[H2|H2]".
    by iDestruct (flipb_opaque_opaque1 with "Hinv H2") as "[]".
  case: t21=> // ?; iDestruct "H1" as "<-".
  by case: t22=> // ?; iDestruct "H2" as "<-".
- move=> t11 IH1 t12 IH2 t21 t22; iIntros "Hinv #H1 #H2".
  rewrite !flipb_lo_termE.
  iDestruct "H1" as "[H1|H1]".
    by iDestruct (flipb_opaque_opaque1 with "Hinv H1") as "[]".
  iDestruct "H2" as "[H2|H2]".
    by iDestruct (flipb_opaque_opaque1 with "Hinv H2") as "[]".
  case: t21=> //= t211 t212; iDestruct "H1" as "[H11 H12]".
  case: t22=> //= t221 t222; iDestruct "H2" as "[H21 H22]".
  iDestruct (IH1 with "Hinv H11 H21") as "%".
  iDestruct (IH2 with "Hinv H12 H22") as "%".
  iPureIntro; congruence.
- move=> l t21 t22; iIntros "Hinv #H1 #H2".
  rewrite !flipb_lo_termE /=.
  iDestruct "H1" as "[H1|H1]"; last by case: t21.
  iDestruct "H2" as "[H2|H2]"; last by case: t22.
  iPoseProof (flipb_opaque_perm with "Hinv H1 H2") as "%E".
  by iPureIntro; apply: val_of_term_inj.
- move=> l t21 t22; iIntros "Hinv #H1 #H2".
  rewrite !flipb_lo_termE /=.
  iDestruct "H1" as "[H1|H1]".
    by iDestruct (flipb_opaque_opaque1 with "Hinv H1") as "[]".
  iDestruct "H2" as "[H2|H2]".
    by iDestruct (flipb_opaque_opaque1 with "Hinv H2") as "[]".
  case: t21=> //= l21; case: t22=> //= l22.
  iDestruct "Hinv" as (?) "[Hsymb _]".
  rewrite !(big_sepL_singleton, big_sepL_cons).
  iDestruct "Hsymb" as "(_ & _ & Hlo_key & _)".
  iPoseProof (flipb_symbol_perm with "Hlo_key H1 H2") as "%E".
  by rewrite E.
- move=> l1 t1 IH t21 t22; iIntros "Hinv #H1 #H2".
  rewrite !flipb_lo_termE.
  iDestruct "H1" as "[H1|H1]"; iDestruct "H2" as "[H2|H2]".
  + iPoseProof (flipb_opaque_perm with "Hinv H1 H2") as "%E".
    iPureIntro; exact: val_of_term_inj.
  + case: t22=> //= l22 t22; iDestruct "H2" as "[H2 _]".
    iPoseProof (flipb_opaque_opaque1 with "Hinv H1") as "#H1' /=".
    iDestruct "H1'" as "[H1' _]".
    iAssert (symbol12 lo_key_name b l1) as "H2'".
      by iRight; iExists l22.
    iDestruct "Hinv" as (TT) "[Hsymb _]".
    rewrite !(big_sepL_singleton, big_sepL_cons).
    iDestruct "Hsymb" as "(_ & _ & Hlo_key & Hhi_key)".
    by iDestruct (symbol_disj with "Hhi_key Hlo_key H1' H2'") as "[]".
  + case: t21=> //= l21 t21; iDestruct "H1" as "[H1 _]".
    iPoseProof (flipb_opaque_opaque1 with "Hinv H2") as "#H2' /=".
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
  opaque_inv -∗
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
  twp_wand


  done.

swp_pure' _.
  iSolveTC.

reshape_expr (eq_term (#0, #n1)%V) ltac:(fun K e' => idtac e').



swp_pure' _.

 iStartProof.


  reshape_expr (eq_term (#0, #n1)%V (#0, #n2)%V) ltac:(fun K' e' =>
    unify e' (eq_term (#0, #n1)%V);
    iApply (swp_bind K' e')
  ).
  iApply swp_rec. apply AsRecV_recv. rewrite /=.
  iApply swp_pure; eauto.
  iApply swp_value. simpl.
  iApply swp_rec. simpl.
  iApply swp_pure; eauto.


iDestruct 1 as "[#Hspec HK]".
  wp_pure_spec E "HK" (App (Val eq_term) _).

  iPoseProof (do_step_pure E j ([AppLCtx (#0, #n2)] ++ K) (eq_term (#0, #n1)%V)) as "?".



  unify (eq_term (#0, #n1)%V (#0, #n2)%V) (App eq_term _).
  lazymatch goal with
  | |- envs_entails ?ENV _ =>
    match ENV with
    | context[Esnoc _ (INamed "HK") (?j ⤇ fill ?K ?e)] =>
      reshape_expr e ltac:(fun K' e' =>
        unify e' (App (Val eq_term) _);
        let H := fresh in
        assert (H := AsRecV_recv);
        iPoseProof (do_step_pure E j (K' ++ K) e' with "[Hspec HK]") as "?";
        [idtac|idtac|idtac |idtac])
    end
  end.
eauto.

  rewrite -[eq_term (#0, #n1)%V (#0, #n2)%V]/(fill [AppLCtx (#0, #n2)%V] (eq_term (#0, #n1)%V)).
  rewrite -fill_app.
  assert (HH := AsRecV_recv).
  iMod (step_rec with "[Hspec HK]") as "H"; try iSolveTC; eauto.
  simpl.



End Terms.
