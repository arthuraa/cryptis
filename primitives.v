From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From crypto Require Import lib term crypto1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition tuple : val := λ: "t1" "t2",
  (#TPair_tag, ("t1", "t2")).

Definition untuple : val := λ: "t",
  if: Fst "t" = #TPair_tag then SOME (Snd "t")
  else NONE.

Notation "'bind:' x := e1 'in' e2" :=
  (match: e1 with SOME x => e2  | NONE => NONE end)%E
  (at level 200, x at level 1, e1, e2 at level 200,
  format "'[' 'bind:'  x  :=  '[' e1 ']'  'in'  '/' e2 ']'") : expr_scope.

Definition term_projV : val := rec: "loop" "t" "n" :=
  if: Fst "t" = #TPair_tag then
    if: "n" = #0 then SOME (Fst (Snd "t"))
    else "loop" (Snd (Snd "t")) ("n" - #1)
  else NONE.

Definition mknonce : val := λ: <>,
  let: "n" := ref #() in
  (#TNonce_tag, "n").

Definition is_key : val := λ: "t",
  if: Fst "t" = #TKey_tag then SOME (Fst (Snd "t"))
  else NONE.

Definition mkakey : val := λ: <>,
  let: "k" := ref #() in
  ((#TKey_tag, (#(int_of_key_type KAEnc), "k")),
   (#TKey_tag, (#(int_of_key_type KADec), "k"))).

Definition aenc : val := λ: "k" "t",
  if: (Fst "k" = #TKey_tag) &&
      (Fst (Snd "k") = #(int_of_key_type KAEnc)) then
    SOME (#TEnc_tag, (#true, Snd (Snd "k"), "t"))
  else NONE.

Definition adec : val := λ: "k" "t",
  if: (Fst "t" = #TEnc_tag)
      && Fst (Fst (Snd "t"))
      && (Snd (Snd "k") = Snd (Fst (Snd "t"))) then
    SOME (Snd (Snd "t"))
  else
    NONE.

Definition mkskey : val := λ: <>,
  let: "k" := ref #() in
  (#TKey_tag, (#(int_of_key_type KSym), "k")).

Definition senc : val := λ: "k" "t",
  (#TEnc_tag, (#false, Snd (Snd "k"), "t")).

Definition sdec : val := λ: "k" "t",
  if: (Fst "t" = #TEnc_tag)
      && (~ Fst (Fst (Snd "t")))
      && (Snd (Snd "k") = Snd (Fst (Snd "t"))) then
    SOME (Snd (Snd "t"))
  else
    NONE.

Definition eq_term : val := (rec: "eq" "x" "y" :=
  if: (Fst "x" = #TInt_tag) && (Fst "y" = #TInt_tag) then
    Snd "x" = Snd "y"
  else if: (Fst "x" = #TPair_tag) && (Fst "y" = #TPair_tag) then
    ("eq" (Fst (Snd "x")) (Fst (Snd "y"))) &&
    ("eq" (Snd (Snd "x")) (Snd (Snd "y")))
  else if: (Fst "x" = #TNonce_tag) && (Fst "y" = #TNonce_tag) then
    Snd "x" = Snd "y"
  else if: (Fst "x" = #TKey_tag) && (Fst "y" = #TKey_tag) then
    (Fst (Snd "x") = Fst (Snd "y")) &&
    (Snd (Snd "x") = Snd (Snd "y"))
  else if: (Fst "x" = #TEnc_tag) && (Fst "y" = #TEnc_tag) then
    (Fst (Fst (Snd "x")) = Fst (Fst (Snd "y"))) &&
    (Snd (Fst (Snd "x")) = Snd (Fst (Snd "y"))) &&
    ("eq" (Snd (Snd "x")) (Snd (Snd "y")))
  else #false)%V.

Section Proofs.

Context `{!heapG Σ, !resG Σ}.

Implicit Types E : coPset.
Implicit Types l : loc.
Implicit Types rs : readers.
Implicit Types t : term.
Implicit Types v : val.

Lemma twp_tuple E t1 t2 :
  ⊢ WP tuple t1 t2 @ E
       [{v, ⌜v = TPair t1 t2⌝}].
Proof. by rewrite val_of_termE /tuple; wp_pures. Qed.

Lemma twp_untuple E t :
  ⊢ WP untuple t @ E
       [{v, ⌜v = match t with
                 | TPair t1 t2 => SOMEV (t1, t2)
                 | _ => NONEV
                 end⌝}].
Proof.
rewrite val_of_termE /untuple.
by case: t=> *; wp_pures.
Qed.

Lemma twp_term_projV E t (n : nat) :
  ⊢ WP term_projV t #n @ E
       [{v, ⌜v = repr (term_proj t n)⌝}].
Proof.
rewrite val_of_termE; elim: t n; try by move=> *; wp_rec; wp_pures.
move=> t1 IH1 t2 IH2 [|n]; wp_rec; wp_pures.
  by rewrite -val_of_termE.
rewrite (_ : (S n - 1)%Z = n) /=; try lia.
by iApply IH2.
Qed.

Lemma twp_mknonce E rs :
  wf_readers rs -∗
  WP mknonce #()%V @ E
     [{v, ∃ l, ⌜v = TNonce l⌝ ∗ nonceT rs l
               ∗ meta_token l (⊤ ∖ ↑cryptoN.@"res")}].
Proof.
iIntros "#wf_rs"; rewrite /mknonce.
wp_pures; wp_bind (ref _)%E; iApply twp_alloc=> //.
iIntros (l) "[Hl Hmeta]".
rewrite (meta_token_difference l (↑cryptoN.@"res")) //.
iDestruct "Hmeta" as "[Hmeta1 Hmeta2]".
iMod (res_alloc (RNonce rs) l with "Hmeta1 wf_rs") as "Hinv"=> //.
by wp_pures; rewrite val_of_termE; eauto.
Qed.

Lemma twp_mkakey E rs_enc rs_dec Φ :
  wf_readers rs_enc -∗
  wf_readers rs_dec -∗
  WP mkakey #()%V @ E
     [{v, ∃ l, ⌜v = (TKey KAEnc l, TKey KADec l)%V⌝
               ∗ akeyT rs_enc rs_dec Φ l
               ∗ meta_token l (⊤ ∖ ↑cryptoN.@"res")}].
Proof.
iIntros "#wf_enc #wf_dec"; rewrite /mkakey.
wp_pures; wp_bind (ref _)%E; iApply twp_alloc=> //.
iIntros (l) "[Hl Hmeta]".
rewrite (meta_token_difference l (↑cryptoN.@"res")) //.
iDestruct "Hmeta" as "[Hmeta1 Hmeta2]".
iMod (res_alloc (RAKey rs_enc rs_dec Φ) l
        with "Hmeta1 [wf_enc wf_dec]") as "[Hinv Hown]"=> //.
  by rewrite wf_resE; iSplit.
wp_pures; rewrite val_of_termE /=; iExists l; iSplit; eauto. 
by repeat iSplit.
Qed.

Definition maybe_keyT rs Φ t : iProp Σ :=
  match t with
  | TKey kt l => keyT kt rs Φ l
  | _ => True
  end.

Definition key_readers t : readers :=
  match t with
  | TKey kt l => {[l]}
  | _ => ∅
  end.

Lemma twp_aenc E rs Φ tk t  :
  maybe_keyT rs Φ tk -∗
  □ Φ t ∗ termT (key_readers tk) t ∨ ⌜rs = RPub⌝ ∗ termT RPub t -∗
  WP aenc tk t @ E
     [{v, match tk with
          | TKey KAEnc l =>
            ⌜v = SOMEV (TEnc true l t)⌝ ∗ termT RPub (TEnc true l t)
          | _ => ⌜v = NONEV⌝
          end}].
Proof.
rewrite val_of_termE /= /aenc; iIntros "Hl Ht".
case: tk; try by move=> *; wp_pures; eauto.
by case=> *; wp_pures; eauto.
Qed.

Lemma wp_aenc E rs Φ tk t  :
  maybe_keyT rs Φ tk -∗
  ▷ (□ Φ t ∗ termT (key_readers tk) t ∨ ⌜rs = RPub⌝ ∗ termT RPub t) -∗
  WP aenc tk t @ E
     {{v, match tk with
          | TKey KAEnc l =>
            ⌜v = SOMEV (TEnc true l t)⌝ ∗ termT RPub (TEnc true l t)
          | _ => ⌜v = NONEV⌝
          end}}.
Proof.
rewrite val_of_termE /= /aenc; iIntros "Hl Ht".
case: tk; try by move=> *; wp_pures; eauto.
by case=> *; wp_pures; eauto.
Qed.

Lemma twp_aencL E Φ tk t :
  maybe_keyT RPub Φ tk -∗
  termT RPub t -∗
  WP aenc tk t @ E
     [{v, match tk with
          | TKey KAEnc l =>
            ⌜v = SOMEV (TEnc true l t)⌝ ∗ termT RPub (TEnc true l t)
          | _ => ⌜v = NONEV⌝
          end}].
Proof.
iIntros "Hl Ht"; iApply (twp_aenc with "Hl"); eauto.
Qed.

Lemma twp_aencH E rs Φ l t :
  keyT KAEnc rs Φ l -∗
  □ Φ t -∗
  termT {[l]} t -∗
  WP aenc (TKey KAEnc l) t @ E
     [{v, ⌜v = SOMEV (TEnc true l t)⌝ ∗ termT RPub (TEnc true l t)}].
Proof.
iIntros "Hl Ht1 Ht2".
by iApply (twp_aenc _ _ _ (TKey KAEnc l) with "Hl"); eauto.
Qed.

Lemma wp_aencH E rs Φ l t :
  keyT KAEnc rs Φ l -∗
  ▷ □ Φ t -∗
  ▷ termT {[l]} t -∗
  WP aenc (TKey KAEnc l) t @ E
     {{v, ⌜v = SOMEV (TEnc true l t)⌝ ∗ termT RPub (TEnc true l t)}}.
Proof.
iIntros "Hl Ht1 Ht2".
iApply (wp_aenc _ _ _ (TKey KAEnc l) with "Hl"); eauto.
Qed.

Lemma twp_adec E rs_enc rs_dec Φ l rs_t t :
  akeyT rs_enc rs_dec Φ l -∗
  termT rs_t t -∗
  WP adec (TKey KADec l) t @ E
     [{v, match t with
          | TEnc true l' t' =>
            if decide (l' = l) then
              ⌜v = SOMEV t'⌝ ∗
              (□ Φ t' ∗ termT {[l]} t' ∨ ⌜rs_enc = RPub⌝ ∗ termT RPub t')
            else
              ⌜v = NONEV⌝
          | _ => ⌜v = NONEV⌝
          end}].
Proof.
rewrite val_of_termE /= /adec; iIntros "Hl Ht".
case: t; try by move=> *; wp_pures.
move=> b l' t' /=; wp_pures.
case: b=> /=; wp_pures; eauto.
iDestruct "Ht" as (rs_enc' Φ') "[Hl' Ht']".
iDestruct "Hl'" as (rs_dec') "Hl'".
destruct decide as [->|ne].
- rewrite bool_decide_true //.
  wp_pures; iSplit=> //.
  iPoseProof (resT_agree with "Hl Hl'") as "#He".
  rewrite res_equivI; iDestruct "He" as "(-> & -> & HΦ)".
  by rewrite ofe_morO_equivI; iRewrite ("HΦ" $! t'); eauto.
- rewrite bool_decide_false; last by congruence.
  by wp_pures.
Qed.

Lemma twp_adecH E rs_enc rs_dec Φ l rs_t t :
  akeyT (RPriv rs_enc) rs_dec Φ l -∗
  termT rs_t t -∗
  WP adec (TKey KADec l) t @ E
     [{v, match t with
          | TEnc true l' t' =>
            if decide (l' = l) then
              ⌜v = SOMEV t'⌝ ∗ □ Φ t' ∗ termT {[l]} t'
            else
              ⌜v = NONEV⌝
          | _ => ⌜v = NONEV⌝
          end}].
Proof.
iIntros "Hl Ht".
iPoseProof (twp_adec with "Hl Ht") as "wp".
iApply (twp_wand with "wp").
iIntros (v) "Ht".
case: t; eauto.
case; eauto.
move=> l' t'; destruct decide as [->|ne]; trivial.
iDestruct "Ht" as "[?[?|[%?]]]"; by iFrame.
Qed.

Lemma twp_is_akey E t :
  ⊢ WP is_key t @ E
       [{v, ⌜v = match t with
                 | TKey kt l => SOMEV #(int_of_key_type kt)
                 | _ => NONEV
                 end⌝}].
Proof.
rewrite val_of_termE /is_key.
by case: t=> *; wp_pures.
Qed.

Lemma twp_mkskey E rs Φ :
  wf_readers rs -∗
  WP mkskey #()%V @ E
     [{v, ∃ l, ⌜v = TKey KSym l⌝ ∗ skeyT rs Φ l
               ∗ meta_token l (⊤ ∖ ↑cryptoN.@"res")}].
Proof.
iIntros "#wf_rs"; rewrite /mkskey.
wp_pures; wp_bind (ref _)%E; iApply twp_alloc=> //.
iIntros (l) "[Hl Hmeta]".
rewrite (meta_token_difference l (↑cryptoN.@"res")) //.
iDestruct "Hmeta" as "[Hmeta1 Hmeta2]".
iMod (res_alloc (RSKey rs Φ) l
        with "Hmeta1 wf_rs") as "#Hres"=> //.
by wp_pures; rewrite val_of_termE; iExists l; repeat iSplit=> //.
Qed.

Lemma twp_senc E rs Φ l t :
  skeyT rs Φ l -∗
  (□ Φ t ∗ termT {[l]} t ∨ ⌜rs = RPub⌝ ∗ termT RPub t) -∗
  WP senc (TKey KSym l) t @ E
     [{v, ⌜v = TEnc false l t⌝ ∗ termT RPub (TEnc false l t)}].
Proof.
rewrite val_of_termE /= /senc; iIntros "Hl Ht".
wp_pures; iSplit=> //.
by iExists rs, Φ; iFrame.
Qed.

Lemma twp_sencL E rs Φ l t :
  skeyT RPub Φ l -∗
  termT RPub t -∗
  WP senc (TKey KSym l) t @ E
     [{v, ⌜v = TEnc false l t⌝ ∗ termT RPub (TEnc false l t)}].
Proof.
iIntros "Hl Ht"; iApply (twp_senc with "Hl"); eauto.
Qed.

Lemma twp_sencH E rs Φ l t :
  skeyT rs Φ l -∗
  □ Φ t -∗
  termT {[l]} t -∗
  WP senc (TKey KSym l) t @ E
     [{v, ⌜v = TEnc false l t⌝ ∗ termT RPub (TEnc false l t)}].
Proof.
iIntros "Hl Ht1 Ht2"; iApply (twp_senc with "Hl"); eauto.
Qed.

Lemma twp_sdec E rs Φ l rs_t t :
  skeyT rs Φ l -∗
  termT rs_t t -∗
  WP sdec (TKey KSym l) t @ E
     [{v, match t with
          | TEnc false l' t' =>
            if decide (l' = l) then
              ⌜v = SOMEV t'⌝ ∗
              (□ Φ t' ∗ termT {[l]} t' ∨ ⌜rs = RPub⌝ ∗ termT RPub t')
            else
              ⌜v = NONEV⌝
          | _ => ⌜v = NONEV⌝
          end}].
Proof.
rewrite val_of_termE /= /sdec; iIntros "Hl Ht".
case: t; try by move=> *; wp_pures.
move=> b l' t' /=; wp_pures.
case: b=> /=; wp_pures; eauto.
iDestruct "Ht" as (rs' Φ') "[Hl' Ht']".
destruct decide as [->|ne].
- rewrite bool_decide_true //.
  wp_pures; iSplit=> //.
  iPoseProof (resT_agree with "Hl Hl'") as "He".
  rewrite res_equivI; iDestruct "He" as "(-> & HΦ)".
  by rewrite ofe_morO_equivI; iRewrite ("HΦ" $! t'); eauto.
- rewrite bool_decide_false; last by congruence.
  by wp_pures.
Qed.

Lemma twp_sdecH E rd Φ l rs_t t :
  skeyT (RPriv rd) Φ l -∗
  termT rs_t t -∗
  WP sdec (TKey KSym l) t @ E
     [{v, match t with
          | TEnc false l' t' =>
            if decide (l' = l) then
              ⌜v = SOMEV t'⌝ ∗ □ Φ t' ∗ termT {[l]} t'
            else
              ⌜v = NONEV⌝
          | _ => ⌜v = NONEV⌝
          end}].
Proof.
iIntros "Hl Ht".
iPoseProof (twp_sdec with "Hl Ht") as "wp".
iApply (twp_wand with "wp").
iIntros (v) "Ht".
case: t; eauto.
case; eauto.
move=> l' t'; destruct decide as [->|ne]; trivial.
iDestruct "Ht" as "[?[?|[%?]]]"; by iFrame.
Qed.

Lemma twp_eq_term E t1 t2 :
  ⊢ WP (eq_term t1 t2) @ E [{ v, ⌜v = #(bool_decide (t1 = t2))⌝ }].
Proof.
rewrite val_of_termE.
elim: t1 t2=> [n1|t11 IH1 t12 IH2|l1|kt1 l1|b1 l1 t1 IH1];
case=> [n2|t21 t22|l2|kt2 l2|b2 l2 t2] /=;
wp_rec; wp_pures=> //.
- iPureIntro; congr (# (LitBool _)).
  apply: bool_decide_iff; intuition congruence.
- wp_bind (eq_term _ _).
  iPoseProof (IH1 t21) as "IH1"; iPoseProof (IH2 t22) as "IH2".
  iApply (twp_wand with "IH1"); iIntros (?) "->".
  case: bool_decide_reflect=> e1.
  + wp_pures; iApply (twp_wand with "IH2"); iIntros (?) "->".
    iPureIntro; congr (# (LitBool _)).
    apply: bool_decide_iff; intuition congruence.
  + wp_pures; iPureIntro; congr (# (LitBool _)).
    rewrite bool_decide_false; congruence.
- iPureIntro; congr (# (LitBool _)).
  apply: bool_decide_iff; intuition congruence.
- case: bool_decide_reflect=> [[/int_of_key_type_inj e1]|e1].
  + wp_pures; iPureIntro; congr (# (LitBool _)).
    apply: bool_decide_iff; intuition congruence.
  + wp_pures; iPureIntro; congr (# (LitBool _)).
    rewrite bool_decide_false; congruence.
- case: bool_decide_reflect=> e1; wp_pures; last first.
    rewrite bool_decide_false //; congruence.
  case: bool_decide_reflect=> e2; wp_pures; last first.
    rewrite bool_decide_false //; congruence.
  iPoseProof (IH1 t2) as "IH1".
  iApply (twp_wand with "IH1"); iIntros (?) "->".
  iPureIntro; congr (# (LitBool _)).
  apply: bool_decide_iff; intuition congruence.
Qed.

End Proofs.
