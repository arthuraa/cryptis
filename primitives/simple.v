From mathcomp Require Import ssreflect.
From mathcomp Require order.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap reservation_map.
From iris.base_logic.lib Require Import invariants saved_prop.
From iris.program_logic Require Import atomic.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import nondet_bool ticket_lock.
From cryptis Require Import lib term cryptis.
From cryptis.primitives Require Import notations comp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Existing Instance ticket_lock.

Definition nondet_nat_loop : val := rec: "loop" "n" :=
  if: nondet_bool #() then "n" else "loop" ("n" + #1).

Definition nondet_nat : val := λ: <>, nondet_nat_loop #0.

Definition nondet_int : val := λ: <>,
  let: "n" := nondet_nat #() in
  if: nondet_bool #() then "n" else - "n".

Definition get_chan : val := λ: "c" "lock", rec: "loop" <> :=
  let: "n" := nondet_nat #() in
  acquire "lock";;
  let: "ts" := !"c" in
  release "lock";;
  match: get_list "ts" "n" with
    NONE => "loop" #()
  | SOME "t" => "t"
  end.

Definition put_chan : val := λ: "c" "lock" "t",
  acquire "lock";;
  "c" <- "t" :: !"c";;
  release "lock".

Definition mkchannel : val := λ: <>,
  let: "c" := ref []%V in
  let: "lock" := newlock #() in
  (put_chan "c" "lock", get_chan "c" "lock").

Definition send : val := λ: "c", Fst "c".
Definition recv : val := λ: "c", Snd "c" #().

Definition tint : val := λ: "n",
  (#TInt_tag, "n").

Definition to_int : val := λ: "t",
  if: Fst "t" = #TInt_tag then SOME (Snd "t")
  else NONE.

Definition tuple : val := λ: "t1" "t2",
  (#TPair_tag, ("t1", "t2")).

Definition untuple : val := λ: "t",
  if: Fst "t" = #TPair_tag then SOME (Snd "t")
  else NONE.

Definition list_of_term : val := rec: "loop" "t" :=
  if: Fst "t" = #TInt_tag then
    if: Snd "t" = #0 then SOMEV NONEV else NONEV
  else if: Fst "t" = #TPair_tag then
    let: "t" := Snd "t" in
    bind: "l" := "loop" (Snd "t") in
    SOME (SOME (Fst "t", "l"))
  else NONE.

Definition term_of_list : val := rec: "loop" "l" :=
  match: "l" with NONE => (#TInt_tag, #0)
  | SOME "p" => tuple (Fst "p") ("loop" (Snd "p"))
  end.

Definition tag (N : namespace) : val := λ: "t",
  tuple (TInt (Zpos (encode N))) "t".

Definition untag (N : namespace) : val := λ: "t",
  bind: "t" := untuple "t" in
  bind: "tag" := to_int (Fst "t") in
  if: "tag" = #(Zpos (encode N))then SOME (Snd "t") else NONE.

Definition mknonce : val := λ: <>,
  let: "n" := ref #() in
  (#TNonce_tag, "n").

Definition is_key : val := λ: "t",
  if: Fst "t" = #TKey_tag then SOME (Fst (Snd "t"))
  else NONE.

Definition seal : val := λ: "k" "t", (#TSeal_tag, ("k", "t")).

Definition hash : val := λ: "t", (#THash_tag, "t").

Definition key kt : val := λ: "k",
  (#TKey_tag, (#(int_of_key_type kt), "k")).

Definition open : val := λ: "k" "t",
  if: (Fst "k" = #TKey_tag)
      && (Fst (Snd "k") = #(int_of_key_type Open))
      && (Fst "t" = #TSeal_tag)
      && (eq_term (key Seal (Snd (Snd "k"))) (Fst (Snd "t"))) then
    SOME (Snd (Snd "t"))
  else
    NONE.

Definition enc c : val := λ: "k" "t",
  seal "k" (tag c "t").

Definition dec c : val := λ: "k" "t",
  bind: "t" := open "k" "t" in
  untag c "t".

Definition mkkeys : val := λ: "k",
  (key Seal "k", key Open "k").

Definition mkakey : val := λ: <>,
  let: "n" := mknonce #() in
  tag (nroot.@"keys".@"enc") "n".

Definition mksigkey : val := λ: <>,
  let: "n" := mknonce #() in
  tag (nroot.@"keys".@"sig") "n".

Definition derive_key : val := λ: "k",
  tag (nroot.@"keys".@"sym") "k".

Definition pkey : val := λ: "sk", key Seal "sk".

Definition aenc c : val := λ: "pk" "t",
  enc c "pk" "t".

Definition adec c : val := λ: "sk" "t",
  dec c (key Open "sk") "t".

Definition senc c : val := λ: "sk" "t",
  enc c (key Seal "sk") "t".

Definition sdec c : val := λ: "sk" "t",
  dec c (key Open "sk") "t".

Definition vkey : val := λ: "sk", key Open "sk".

Definition sign c : val := λ: "sk" "t",
  enc c (key Seal "sk") "t".

Definition verify c : val := λ: "vk" "t",
  dec c "vk" "t".

Definition to_seal_key : val := λ: "t",
  bind: "kt" := is_key "t" in
  guard: ("kt" = repr Seal) in
  SOME "t".

Definition to_open_key : val := λ: "t",
  bind: "kt" := is_key "t" in
  guard: ("kt" = repr Open) in
  SOME "t".

Section Proofs.

Context `{!heapGS Σ, !cryptisGS Σ}.
Notation nonce := loc.

Implicit Types E : coPset.
Implicit Types a : nonce.
Implicit Types t : term.
Implicit Types v : val.
Implicit Types Φ : prodO locO termO -n> iPropO Σ.
Implicit Types Ψ : val → iProp Σ.
Implicit Types N : namespace.

Lemma wp_nondet_nat_loop Ψ (m : nat) :
  (∀ n : nat, Ψ #n) ⊢
  WP nondet_nat_loop #m {{ Ψ }}.
Proof.
iIntros "post"; iLöb as "IH" forall (m); wp_rec.
wp_apply nondet_bool_spec => //.
iIntros "%b _"; case: b; wp_if; first by iApply "post".
wp_pures. have -> : (m + 1)%Z = (m + 1)%nat by lia.
by iApply "IH".
Qed.

Lemma wp_nondet_nat Ψ :
  (∀ n : nat, Ψ #n) ⊢
  WP nondet_nat #() {{ Ψ }}.
Proof.
iIntros "post". wp_lam. by wp_apply (wp_nondet_nat_loop _ 0).
Qed.

Lemma wp_nondet_int Ψ :
  (∀ n : Z, Ψ #n) ⊢
  WP nondet_int #() {{ Ψ }}.
Proof.
iIntros "post"; rewrite /nondet_int; wp_pures.
wp_apply wp_nondet_nat. iIntros "%n"; wp_pures.
wp_apply nondet_bool_spec => //. iIntros "%b _".
case: b; wp_if; first by iApply "post".
by wp_pures; iApply "post".
Qed.

Definition channel c : iProp Σ :=
  ∃ (sf rf : val), ⌜c = (sf, rf)%V⌝ ∗
    □ (∀ t Ψ, public t -∗ Ψ #() -∗ WP sf t {{ Ψ }}) ∗
    □ (∀ Ψ, (∀ t, public t -∗ Ψ t) -∗ WP rf #() {{ Ψ }}).

Global Instance channel_persistent c : Persistent (channel c).
Proof. apply _. Qed.

Definition chan_inv (c : loc) : iProp Σ :=
  ∃ ts : list term, c ↦ repr ts ∗ [∗ list] t ∈ ts, public t.

Lemma wp_mkchannel `{!tlockG Σ} Ψ :
  (∀ c, channel c -∗ Ψ c) ⊢
  WP mkchannel #() {{ Ψ }}.
Proof.
iIntros "post".
wp_lam; wp_apply (wp_nil (A := term)).
wp_alloc c as "cP"; wp_pures.
wp_apply (newlock_spec (chan_inv c) with "[cP]").
  by iExists []; iSplit => //.
iIntros "%lk %γ #lkP"; rewrite /get_chan /put_chan; wp_pures.
iModIntro; iApply "post". clear Ψ. iExists _, _; do 2!iSplit => //.
- iIntros "!> %t %Ψ #p_t post".
  wp_pures. wp_apply acquire_spec => //. iIntros "[locked inv]".
  iDestruct "inv" as (ts) "[c_ts #tsP]".
  wp_pures; wp_load.
  wp_apply wp_cons. wp_store.
  wp_apply (release_spec with "[$locked c_ts]").
  { iSplit => //. iExists (t :: ts). iFrame.
    rewrite big_sepL_cons. eauto. }
  by iIntros "_".
- iLöb as "IH".
  iIntros "!> %Ψ post".
  wp_rec. wp_apply wp_nondet_nat. iIntros "%n". wp_pures.
  wp_apply (acquire_spec with "lkP") => //.
  iIntros "[locked inv]".
  iDestruct "inv" as (ts) "[c_ts #tsP]".
  wp_pures; wp_load.
  wp_pures; wp_apply (release_spec with "[$locked c_ts]").
  { iSplit => //. iExists ts; eauto. }
  iIntros "_". wp_pures. wp_apply wp_get_list.
  case ts_n: (ts !! n) => [t'|].
  { wp_pures. iApply "post". rewrite big_sepL_forall. by iApply "tsP". }
  wp_pure _. wp_pure _. wp_pure _.
  iApply ("IH" with "post").
Qed.

Lemma wp_send c t Ψ :
  channel c -∗
  ▷ public t -∗
  Ψ #() -∗
  WP send c t {{ Ψ }}.
Proof.
iDestruct 1 as (sf cf) "#(-> & H & _)".
iIntros "#??"; rewrite /send; wp_pures.
by iApply "H".
Qed.

Lemma wp_recv c Ψ :
  channel c -∗
  (∀ t, public t -∗ Ψ t) -∗
  WP recv c {{ Ψ }}.
Proof.
iDestruct 1 as (sf cf) "#(-> & _ & H)".
iIntros "?"; rewrite /recv; wp_pures.
by iApply "H".
Qed.

Lemma twp_tint E Ψ n : Ψ (TInt n) ⊢ WP tint #n @ E [{ Ψ }].
Proof.
by rewrite /tint val_of_term_unseal; iIntros "Hpost"; wp_pures.
Qed.

Lemma wp_tint E Ψ n : Ψ (TInt n) ⊢ WP tint #n @ E {{ Ψ }}.
Proof. by iIntros "?"; iApply twp_wp; iApply twp_tint. Qed.

Lemma twp_to_int E t Ψ :
  Ψ (repr (Spec.to_int t)) ⊢
  WP to_int t @ E [{ Ψ }].
Proof.
rewrite /to_int val_of_term_unseal; iIntros "Hpost"; wp_pures.
case: t; by move=> *; wp_pures; eauto.
Qed.

Lemma wp_to_int E t Ψ :
  Ψ (repr (Spec.to_int t)) ⊢
  WP to_int t @ E {{ Ψ }}.
Proof.
by iIntros "?"; iApply twp_wp; iApply twp_to_int.
Qed.

Lemma twp_tuple E t1 t2 Ψ :
  Ψ (TPair t1 t2) ⊢
  WP tuple t1 t2 @ E [{ Ψ }].
Proof.
rewrite val_of_term_unseal /tuple; by iIntros "?"; wp_pures.
Qed.

Lemma wp_tuple E t1 t2 Ψ :
  Ψ (TPair t1 t2) ⊢
  WP tuple t1 t2 @ E {{ Ψ }}.
Proof.
by iIntros "?"; iApply twp_wp; iApply twp_tuple.
Qed.

Lemma twp_untuple E t Ψ :
  Ψ (repr (Spec.untuple t)) ⊢
  WP untuple t @ E [{ Ψ }].
Proof.
iIntros "post".
rewrite /Spec.untuple /untuple /= val_of_term_unseal.
case: t; by move=> *; wp_pures; iApply "post".
Qed.

Lemma wp_untuple E t Ψ :
  Ψ (repr (Spec.untuple t)) ⊢
  WP untuple t @ E {{ Ψ }}.
Proof.
by iIntros "?"; iApply twp_wp; iApply twp_untuple.
Qed.

Lemma twp_term_of_list E ts Ψ :
  Ψ (repr (Spec.of_list ts)) ⊢
  WP term_of_list (repr ts) @ E [{ Ψ }].
Proof.
rewrite /= [in repr_list ts]repr_list_unseal Spec.of_list_unseal.
elim: ts Ψ => [|t ts IH] Ψ /=; iIntros "post"; wp_rec; wp_pures.
  by rewrite val_of_term_unseal.
wp_bind (term_of_list _); iApply IH; wp_pures.
by iApply twp_tuple.
Qed.

Lemma wp_term_of_list E ts Ψ :
  Ψ (repr (Spec.of_list ts)) ⊢
  WP term_of_list (repr ts) @ E {{ Ψ }}.
Proof.
by iIntros "?"; iApply twp_wp; iApply twp_term_of_list.
Qed.

Lemma twp_list_of_term E t Ψ :
  Ψ (repr (Spec.to_list t)) ⊢
  WP list_of_term t @ E [{ Ψ }].
Proof.
rewrite val_of_term_unseal /= repr_list_unseal.
elim/term_ind': t Ψ;
try by move=> *; iIntros "post"; wp_rec; wp_pures; iApply "post".
  move=> n Ψ /=; iIntros "post"; wp_rec; wp_pures.
  case: bool_decide_reflect => [[->]|]; first by wp_pures.
  case: n => *; by wp_pures.
move=> thead _ trest IH Ψ /=; iIntros "post".
wp_rec; wp_pures; wp_bind (list_of_term _); iApply IH.
case: (Spec.to_list trest) => [ts|] /=; wp_pures; eauto.
by rewrite -val_of_term_unseal.
Qed.

Lemma wp_list_of_term E t Ψ :
  Ψ (repr (Spec.to_list t)) ⊢
  WP list_of_term t @ E {{ Ψ }}.
Proof.
by iIntros "?"; iApply twp_wp; iApply twp_list_of_term.
Qed.

Lemma twp_list `{!Repr A} (xs : list A) E Ψ :
  Ψ (repr xs) ⊢
  WP list_to_expr xs @ E [{ Ψ }].
Proof.
elim: xs Ψ => [|x xs IH] /= Ψ; iIntros "post".
  by iApply (@twp_nil A _).
wp_bind (list_to_expr _); iApply IH.
by iApply (@twp_cons A).
Qed.

Lemma wp_list `{!Repr A} (xs : list A) E Ψ :
  Ψ (repr xs) ⊢
  WP list_to_expr xs @ E {{ Ψ }}.
Proof. by iIntros "?"; iApply twp_wp; iApply twp_list. Qed.

Lemma twp_tag E N t Ψ :
  Ψ (repr (Spec.tag N t)) ⊢
  WP tag N t @ E [{ Ψ }].
Proof.
iIntros "post".
by rewrite Spec.tag_unseal /tag; wp_pures; iApply twp_tuple.
Qed.

Lemma wp_tag E N t Ψ :
  Ψ (repr (Spec.tag N t)) ⊢
  WP tag N t @ E {{ Ψ }}.
Proof.
iIntros "post".
by rewrite Spec.tag_unseal /tag; wp_pures; iApply wp_tuple.
Qed.

Lemma twp_untag E N t Ψ :
  Ψ (repr (Spec.untag N t)) ⊢
  WP untag N t @ E [{ Ψ }].
Proof.
iIntros "post".
rewrite Spec.untag_unseal /untag /=; wp_pures.
wp_bind (untuple _); iApply twp_untuple.
case: t; try by [move=> *; wp_pures; iApply "post"].
move=> t1 t2; wp_pures.
wp_bind (to_int _); iApply twp_to_int.
case: t1; try by [move=> *; wp_pures; iApply "post"].
move=> n'; wp_pures.
case: bool_decide_reflect => [[->]|ne]; wp_pures.
  by rewrite decide_True_pi.
case: n' ne; try by move=> *; iApply "post".
move=> n' ne; case: decide => e; try iApply "post".
congruence.
Qed.

Lemma wp_untag E N t Ψ :
  Ψ (repr (Spec.untag N t)) ⊢
  WP untag N t @ E {{ Ψ }}.
Proof.
by iIntros "?"; iApply twp_wp; iApply twp_untag.
Qed.

Lemma twp_mknonce_gen (P Q : term → iProp Σ) E Ψ (Φ : term → iProp Σ) :
  (∀ t, (minted t -∗ False) ∧
        (|==> minted t ∗
              □ (public t ↔ ▷ □ P t) ∗
              □ (∀ t', dh_pred t t' ↔ ▷ □ Q t')) ={E}=∗
        minted t ∗
        □ (public t ↔ ▷ □ P t) ∗
        □ (∀ t', dh_pred t t' ↔ ▷ □ Q t') ∗
        Φ t) -∗
  (∀ t, ⌜is_nonce t⌝ -∗
        minted t -∗
        □ (public t ↔ ▷ □ P t) -∗
        □ (∀ t', dh_pred t t' ↔ ▷ □ Q t') -∗
        Φ t -∗
        Ψ t) -∗
  WP mknonce #()%V @ E [{ Ψ }].
Proof.
rewrite /mknonce; iIntros "mint post".
wp_pures; wp_bind (ref _)%E; iApply twp_alloc=> //.
iIntros (a) "[_ token]".
iPoseProof (nonce_alloc P Q with "token") as "fresh".
iPoseProof ("mint" with "fresh") as ">(#? & #? & #? & ?)".
iSpecialize ("post" $! (TNonce a)).
wp_pures. rewrite val_of_term_unseal /=.
iApply ("post" with "[] [] [] [$]"); eauto.
Qed.

Lemma wp_mknonce_gen (P Q : term → iProp Σ) E Ψ (Φ : term → iProp Σ) :
  (∀ t, (minted t -∗ False) ∧
        (|==> minted t ∗
              □ (public t ↔ ▷ □ P t) ∗
              □ (∀ t', dh_pred t t' ↔ ▷ □ Q t')) ={E}=∗
        minted t ∗
        □ (public t ↔ ▷ □ P t) ∗
        □ (∀ t', dh_pred t t' ↔ ▷ □ Q t') ∗
        Φ t) -∗
  (∀ t, ⌜is_nonce t⌝ -∗
        minted t -∗
        □ (public t ↔ ▷ □ P t) -∗
        □ (∀ t', dh_pred t t' ↔ ▷ □ Q t') -∗
        Φ t -∗
        Ψ t) -∗
  WP mknonce #()%V @ E {{ Ψ }}.
Proof.
iIntros "H1 H2". iApply twp_wp.
iApply (twp_mknonce_gen with "H1 H2").
Qed.

Lemma twp_mknonce_freshN (T : gset term) (P Q : term → iProp Σ) (T' : term → gset term) Ψ :
  cryptis_ctx -∗
  (∀ t, ⌜t ∈ T⌝ -∗ minted t) -∗
  (∀ t, [∗ set] t' ∈ T' t, □ (minted t ↔ minted t')) -∗
  (∀ t, ⌜∀ t', t' ∈ T → ¬ subterm t t'⌝ -∗
        ⌜is_nonce t⌝ -∗
        minted t -∗
        □ (public t ↔ ▷ □ P t) -∗
        □ (∀ t', dh_pred t t' ↔ ▷ □ Q t') -∗
        ([∗ set] t' ∈ T' t, term_token t' ⊤) -∗
        Ψ t) -∗
  WP mknonce #()%V [{ Ψ }].
Proof.
iIntros "#ctx minted_T #minted_T' post".
iApply (twp_mknonce_gen P Q ⊤ _
          (λ t, ⌜∀ t', t' ∈ T → ¬ subterm t t'⌝ ∗
          [∗ set] t' ∈ T' t, term_token t' ⊤)%I
         with "[minted_T] [post]").
{ iIntros "%t fresh".
  iAssert (⌜∀ t', t' ∈ T → ¬ subterm t t'⌝)%I as "%fresh".
  { iIntros "%t' %t'_T %t_t'".
    iPoseProof ("minted_T" $! t' with "[//]") as "#minted_t'".
    iPoseProof (subterm_minted t_t' with "minted_t'") as "minted_t".
    iDestruct "fresh" as "[fresh _]".
    by iApply "fresh". }
  iMod (term_token_alloc (T' t)
          (minted t -∗ False)
          (minted t ∗ □ (public t ↔ ▷ □ P t) ∗
           □ (∀ t', dh_pred t t' ↔ ▷ □ Q t'))
          with "ctx [] [] [fresh]") as "(post & token)" => //.
  - iIntros "%t' %t'_t contra minted_t'". iApply "contra".
    iSpecialize ("minted_T'" $! t).
    rewrite big_sepS_delete //.
    iDestruct "minted_T'" as "[#e _]". by iApply "e".
  - iIntros "%t' %t'_t (minted_t & _)".
    iSpecialize ("minted_T'" $! t).
    rewrite big_sepS_delete //.
    iDestruct "minted_T'" as "[#e _]". by iApply "e".
  - iSplit.
    + by iDestruct "fresh" as "[fresh _]".
    + by iDestruct "fresh" as "[_ >fresh]".
  iFrame. do !iModIntro.
  iDestruct "post" as "(? & ? & ?)". eauto. }
iIntros "% ? ? ? ? [? ?]".
iApply ("post" with "[$] [$] [$] [$] [$] [$]").
Qed.

Lemma wp_mknonce_freshN (T : gset term) P Q (T' : term → gset term) Ψ :
  cryptis_ctx -∗
  (∀ t, ⌜t ∈ T⌝ -∗ minted t) -∗
  (∀ t, [∗ set] t' ∈ T' t, □ (minted t ↔ minted t')) -∗
  (∀ t, ⌜∀ t', t' ∈ T → ¬ subterm t t'⌝ -∗
        ⌜is_nonce t⌝ -∗
        minted t -∗
        □ (public t ↔ ▷ □ P t) -∗
        □ (∀ t', dh_pred t t' ↔ ▷ □ Q t') -∗
        ([∗ set] t' ∈ T' t, term_token t' ⊤) -∗
        Ψ t) -∗
  WP mknonce #()%V {{ Ψ }}.
Proof.
iIntros "#ctx H1 H2 H3".
by iApply twp_wp; iApply (twp_mknonce_freshN with "[//] H1 H2 H3").
Qed.

Lemma twp_mknonce_fresh (T : gset term) (P Q : term → iProp Σ) Ψ :
  cryptis_ctx -∗
  (∀ t, ⌜t ∈ T⌝ -∗ minted t) -∗
  (∀ t, ⌜∀ t', t' ∈ T → ¬ subterm t t'⌝ -∗
        ⌜is_nonce t⌝ -∗
        minted t -∗
        □ (public t ↔ ▷ □ P t) -∗
        □ (∀ t', dh_pred t t' ↔ ▷ □ Q t') -∗
        term_token t ⊤ -∗
        Ψ t) -∗
  WP mknonce #()%V [{ Ψ }].
Proof.
iIntros "#ctx minted_T post".
iApply (twp_mknonce_freshN T P Q (λ t : term, {[t]}) _
         with "[//] minted_T [] [post]") => //.
{ iIntros "%t". rewrite big_sepS_singleton. iModIntro.
  iSplit; by iIntros "?". }
iIntros "% ? ? ? ? ?".
rewrite big_sepS_singleton.
by iApply ("post" with "[$] [$] [$] [$] [$]").
Qed.

Lemma wp_mknonce_fresh (T : gset term) P Q Ψ :
  cryptis_ctx -∗
  (∀ t, ⌜t ∈ T⌝ -∗ minted t) -∗
  (∀ t, ⌜∀ t', t' ∈ T → ¬ subterm t t'⌝ -∗
        ⌜is_nonce t⌝ -∗
        minted t -∗
        □ (public t ↔ ▷ □ P t) -∗
        □ (∀ t', dh_pred t t' ↔ ▷ □ Q t') -∗
        term_token t ⊤ -∗
        Ψ t) -∗
  WP mknonce #()%V {{ Ψ }}.
Proof.
iIntros "#ctx H1 H2".
by iApply twp_wp; iApply (twp_mknonce_fresh with "[//] H1 H2").
Qed.

Lemma twp_mknonce (P Q : term → iProp Σ) Ψ :
  cryptis_ctx -∗
  (∀ t, ⌜is_nonce t⌝ -∗
        minted t -∗
        □ (public t ↔ ▷ □ P t) -∗
        □ (∀ t', dh_pred t t' ↔ ▷ □ Q t') -∗
        term_token t ⊤ -∗
        Ψ t) -∗
  WP mknonce #()%V [{ Ψ }].
Proof.
iIntros "#ctx post". iApply (twp_mknonce_fresh ∅ P Q) => //.
- iIntros "%". rewrite elem_of_empty. iDestruct 1 as "[]".
- iIntros "% _". iApply "post".
Qed.

Lemma wp_mknonce (P Q : term → iProp Σ) Ψ :
  cryptis_ctx -∗
  (∀ t, ⌜is_nonce t⌝ -∗
        minted t -∗
        □ (public t ↔ ▷ □ P t) -∗
        □ (∀ t', dh_pred t t' ↔ ▷ □ Q t') -∗
        term_token t ⊤ -∗
        Ψ t) -∗
  WP mknonce #()%V {{ Ψ }}.
Proof.
iIntros "#ctx H".
by iApply twp_wp; iApply (twp_mknonce with "[//] H").
Qed.

Lemma twp_key kt E (k : term) ψ :
  ψ (TKey kt k : val) ⊢
  WP key kt k @ E [{ ψ }].
Proof.
rewrite val_of_term_unseal /=.
by iIntros "post"; wp_lam; wp_pures.
Qed.

Lemma wp_key kt E (k : term) ψ :
  ψ (TKey kt k : val) ⊢
  WP key kt k @ E {{ ψ }}.
Proof.
rewrite val_of_term_unseal /=.
by iIntros "post"; wp_lam; wp_pures.
Qed.

Lemma twp_mkkeys E (k : term) Ψ :
  Ψ (TKey Seal k, TKey Open k)%V ⊢
  WP mkkeys k @ E [{ Ψ }].
Proof.
rewrite /mkkeys.
iIntros "post"; wp_pures.
wp_apply twp_key.
wp_apply twp_key.
by wp_pures.
Qed.

Lemma wp_mkkeys E (k : term) Ψ :
  Ψ (TKey Seal k, TKey Open k)%V ⊢
  WP mkkeys k @ E {{ Ψ }}.
Proof.
by iIntros "post"; iApply twp_wp; iApply twp_mkkeys.
Qed.

Lemma twp_mkakey Ψ :
  cryptis_ctx -∗
  (∀ t, public (TKey Seal t) -∗
        secret (TKey Open t) -∗
        term_token t ⊤ -∗
        Ψ t) -∗
  WP mkakey #() [{ Ψ }].
Proof.
iIntros "#ctx post". iMod unknown_alloc as (γ) "unknown".
rewrite /mkakey. wp_pures.
wp_bind (mknonce _).
iApply (twp_mknonce_freshN ∅ (λ _, known γ 1) (λ _, False%I)
  (λ t, {[Spec.tag (nroot.@"keys".@"enc") t]})) => //.
- iIntros "% ?". by rewrite elem_of_empty.
- iIntros "%t". rewrite big_sepS_singleton minted_tag.
  iModIntro. by iSplit; iIntros "?".
iIntros "%t %fresh % #s_t #p_t _ token".
rewrite big_sepS_singleton.
pose (t' := Spec.tag (nroot.@"keys".@"enc") t).
iAssert (secret (TKey Open t')) with "[unknown]" as "tP"; first do 2?iSplit.
- iMod (known_alloc with "unknown") as "#known".
  iSpecialize ("p_t" with "known").
  iModIntro. rewrite public_TKey. iLeft. by rewrite public_tag.
- iMod (known_alloc 2 with "unknown") as "#known".
  iIntros "!> !>". iSplit.
  + iIntros "#p_t'".
    iMod (public_enc_keyE with "ctx p_t'") as "contra".
    iPoseProof ("p_t" with "contra") as ">#known'".
    by iPoseProof (known_agree with "known known'") as "%".
  + iIntros "#contra".
    rewrite public_TKey. iLeft. rewrite public_tag.
    iApply "p_t". by iDestruct "contra" as ">[]".
- iIntros "#p_t'".
  iMod (public_enc_keyE with "ctx p_t'") as "contra".
  iPoseProof ("p_t" with "contra") as ">#known".
  by iPoseProof (unknown_known with "[$] [//]") as "[]".
iAssert (minted (TKey Open t')) as "s_t'".
  by rewrite minted_TKey minted_tag.
wp_pures. wp_bind (tag _ _). iApply twp_tag.
iApply ("post" with "[] [$] [$]") => //.
iApply (public_enc_key with "ctx"). by eauto.
Qed.

Lemma wp_mkakey Ψ :
  cryptis_ctx -∗
  (∀ t, public (TKey Seal t) -∗
        secret (TKey Open t) -∗
        term_token t ⊤ -∗
        Ψ t) -∗
  WP mkakey #() {{ Ψ }}.
Proof.
iIntros "#? ?". iApply twp_wp. by wp_apply twp_mkakey.
Qed.

(* FIXME: It should be possible to prove a twp for this, but right now we cannot
generate later credits when proving in a twp, which is required for manipulating
honest_auth. *)

Lemma wp_mkakey_phase n T Ψ :
  cryptis_ctx -∗
  honest n T -∗
  ●Ph n -∗
  (∀ t, public (TKey Seal t) -∗
        honest (S n) (T ∪ {[TKey Open t]}) -∗
        ●Ph (S n) -∗
        term_token t ⊤ -∗
        Ψ t) -∗
  WP mkakey #() {{ Ψ }}.
Proof.
iIntros "#ctx #hon phase post". iMod unknown_alloc as (γ) "unknown".
rewrite /mkakey. wp_pure _ credit:"cred". wp_pures.
iAssert (□ (∀ t, ⌜t ∈ T⌝ → minted t))%I as "#s_T".
  iPoseProof (honest_minted with "hon") as "#?".
  iModIntro. by rewrite -big_sepS_forall.
wp_bind (mknonce _).
iApply (wp_mknonce_freshN T (λ _, known γ 1) (λ _, False%I)
  (λ t, {[Spec.tag (nroot.@"keys".@"enc") t]})) => //.
- iIntros "%t #t_T". by iApply "s_T".
- iIntros "%t". rewrite big_sepS_singleton minted_tag.
  iModIntro. by iSplit; iIntros "?".
iIntros "%t %fresh % #s_t #p_t _ token".
rewrite big_sepS_singleton.
pose (t' := Spec.tag (nroot.@"keys".@"enc") t).
have {}fresh : TKey Open t' ∉ T.
  move=> t'_T; apply: fresh => //.
  apply: STKey. exact: subterm_tag.
iAssert (secret (TKey Open t')) with "[unknown]" as "tP"; first do 2?iSplit.
- iMod (known_alloc with "unknown") as "#known".
  iSpecialize ("p_t" with "known").
  iModIntro. rewrite public_TKey. iLeft. by rewrite public_tag.
- iMod (known_alloc 2 with "unknown") as "#known".
  iIntros "!> !>". iSplit.
  + iIntros "#p_t'".
    iMod (public_enc_keyE with "ctx p_t'") as "contra".
    iPoseProof ("p_t" with "contra") as ">#known'".
    by iPoseProof (known_agree with "known known'") as "%".
  + iIntros "#contra".
    rewrite public_TKey. iLeft. rewrite public_tag.
    iApply "p_t". by iDestruct "contra" as ">[]".
- iIntros "#p_t'".
  iMod (public_enc_keyE with "ctx p_t'") as "contra".
  iPoseProof ("p_t" with "contra") as ">#known".
  by iPoseProof (unknown_known with "[$] [//]") as "[]".
iAssert (minted (TKey Open t')) as "s_t'".
  by rewrite minted_TKey minted_tag.
iMod (honest_insert with "ctx cred hon phase s_t' tP") as "[#hon' phase]" => //.
wp_pures. wp_bind (tag _ _). iApply wp_tag.
iApply ("post" with "[] [$] [$]") => //.
iApply (public_enc_key with "ctx"). by eauto.
Qed.

Lemma twp_mksigkey Ψ :
  cryptis_ctx -∗
  (∀ t, public (TKey Open t) -∗
        secret (TKey Seal t) -∗
        term_token t ⊤ -∗
        Ψ t) -∗
  WP mksigkey #() [{ Ψ }].
Proof.
iIntros "#ctx post". iMod unknown_alloc as (γ) "unknown".
rewrite /mksigkey. wp_pures.
wp_bind (mknonce _).
iApply (twp_mknonce_freshN ∅ (λ _, known γ 1) (λ _, False%I)
  (λ t, {[Spec.tag (nroot.@"keys".@"sig") t]})) => //.
- iIntros "% ?". by rewrite elem_of_empty.
- iIntros "%t". rewrite big_sepS_singleton minted_tag.
  iModIntro. by iSplit; iIntros "?".
iIntros "%t %fresh % #s_t #p_t _ token".
rewrite big_sepS_singleton.
pose (t' := Spec.tag (nroot.@"keys".@"sig") t).
iAssert (secret (TKey Seal t')) with "[unknown]" as "tP"; first do 2?iSplit.
- iMod (known_alloc with "unknown") as "#known".
  iSpecialize ("p_t" with "known").
  iModIntro. rewrite public_TKey. iLeft. by rewrite public_tag.
- iMod (known_alloc 2 with "unknown") as "#known".
  iIntros "!> !>". iSplit.
  + iIntros "#p_t'".
    iMod (public_sig_keyE with "ctx p_t'") as "contra".
    iPoseProof ("p_t" with "contra") as ">#known'".
    by iPoseProof (known_agree with "known known'") as "%".
  + iIntros "#contra".
    rewrite public_TKey. iLeft. rewrite public_tag.
    iApply "p_t". by iDestruct "contra" as ">[]".
- iIntros "#p_t'".
  iMod (public_sig_keyE with "ctx p_t'") as "contra".
  iPoseProof ("p_t" with "contra") as ">#known".
  by iPoseProof (unknown_known with "[$] [//]") as "[]".
iAssert (minted (TKey Seal t')) as "s_t'".
  by rewrite minted_TKey minted_tag.
wp_pures. wp_bind (tag _ _). iApply twp_tag.
iApply ("post" with "[] [$] [$]") => //.
iApply (public_sig_key with "ctx"). by eauto.
Qed.

Lemma wp_mksigkey Ψ :
  cryptis_ctx -∗
  (∀ t, public (TKey Open t) -∗
        secret (TKey Seal t) -∗
        term_token t ⊤ -∗
        Ψ t) -∗
  WP mksigkey #() {{ Ψ }}.
Proof.
iIntros "#? ?". iApply twp_wp. by wp_apply twp_mksigkey.
Qed.

Lemma wp_mksigkey_phase n T Ψ :
  cryptis_ctx -∗
  honest n T -∗
  ●Ph n -∗
  (∀ t, public (TKey Open t) -∗
        honest (S n) (T ∪ {[TKey Seal t]}) -∗
        ●Ph (S n) -∗
        Ψ t) -∗
  WP mksigkey #() {{ Ψ }}.
Proof.
iIntros "#ctx #hon phase post". iMod unknown_alloc as (γ) "unknown".
rewrite /mksigkey. wp_pure _ credit:"cred".
iAssert (□ (∀ t, ⌜t ∈ T⌝ → minted t))%I as "#s_T".
  iPoseProof (honest_minted with "hon") as "#?".
  iModIntro. by rewrite -big_sepS_forall.
wp_bind (mknonce _).
iApply (wp_mknonce_freshN T (λ _, known γ 1) (λ _, False%I)
  (λ t, {[Spec.tag (nroot.@"keys".@"sig") t]})) => //.
- iIntros "%t #t_T". by iApply "s_T".
- iIntros "%t". rewrite big_sepS_singleton minted_tag.
  iModIntro. by iSplit; iIntros "?".
iIntros "%t %fresh % #s_t #p_t _ token".
rewrite big_sepS_singleton.
pose (t' := Spec.tag (nroot.@"keys".@"sig") t).
have {}fresh : TKey Seal t' ∉ T.
  move=> t'_T; apply: fresh => //.
  apply: STKey. exact: subterm_tag.
iAssert (secret (TKey Seal t')) with "[unknown]" as "tP"; first do 2?iSplit.
- iMod (known_alloc with "unknown") as "#known".
  iSpecialize ("p_t" with "known").
  iModIntro. rewrite public_TKey. iLeft. by rewrite public_tag.
- iMod (known_alloc 2 with "unknown") as "#known".
  iIntros "!> !>". iSplit.
  + iIntros "#p_t'". iMod (public_sig_keyE with "ctx p_t'") as "contra".
    iPoseProof ("p_t" with "contra") as ">#known'".
    by iPoseProof (known_agree with "known known'") as "%".
  + iIntros "#contra".
    rewrite public_TKey. iLeft. rewrite public_tag.
    iApply "p_t". by iDestruct "contra" as ">[]".
- iIntros "#p_t'". iMod (public_sig_keyE with "ctx p_t'") as "contra".
  iPoseProof ("p_t" with "contra") as ">#known".
  by iPoseProof (unknown_known with "[$] [//]") as "[]".
iAssert (minted (TKey Seal t')) as "s_t'".
  by rewrite minted_TKey minted_tag.
iMod (honest_insert with "ctx cred hon phase s_t' tP") as "[hon' phase]" => //.
wp_pures. wp_bind (tag _ _). iApply wp_tag.
iApply ("post" with "[] hon'") => //.
iApply (public_sig_key with "ctx"). eauto.
Qed.

Lemma twp_derive_key E (k : term) Ψ :
  Ψ (Spec.derive_key k) ⊢
  WP derive_key k @ E [{ Ψ }].
Proof.
rewrite /derive_key. iIntros "post". wp_pures.
wp_pures. by wp_apply twp_tag.
Qed.

Lemma wp_derive_key E (k : term) Ψ :
  Ψ (Spec.derive_key k) ⊢
  WP derive_key k @ E {{ Ψ }}.
Proof.
by iIntros "post"; iApply twp_wp; iApply twp_derive_key.
Qed.

Lemma twp_seal E t1 t2 Ψ :
  Ψ (TSeal t1 t2) ⊢
  WP seal t1 t2 @ E [{ Ψ }].
Proof.
rewrite !val_of_term_unseal /seal.
iIntros "H".
case: t1; try by move=> *; wp_pures; eauto.
Qed.

Lemma wp_seal E t1 t2 Ψ :
  Ψ (TSeal t1 t2) ⊢
  WP seal  t1 t2 @ E {{ Ψ }}.
Proof. by iIntros "?"; iApply twp_wp; iApply twp_seal. Qed.

Lemma twp_hash E t Ψ : Ψ (THash t) ⊢ WP hash t @ E [{ Ψ }].
Proof.
by rewrite /hash val_of_term_unseal; iIntros "?"; wp_pures.
Qed.

Lemma wp_hash E t Ψ : Ψ (THash t) ⊢ WP hash t @ E {{ Ψ }}.
Proof. by iIntros "?"; iApply twp_wp; iApply twp_hash. Qed.

Lemma twp_open E t1 t2 Ψ :
  Ψ (repr (Spec.open t1 t2)) ⊢
  WP open t1 t2 @ E [{ Ψ }].
Proof.
rewrite /repr /repr_option /repr /repr_term !val_of_term_unseal /open.
iIntros "H".
wp_pures.
case: t1; try by move=> /= *; wp_pures.
case; try by move=> /= *; wp_pures.
move=> tk; wp_pures.
case: t2; try by move=> /= *; wp_pures.
move=> tk' t /=; wp_pures.
rewrite -val_of_term_unseal.
wp_pures.
wp_apply twp_key. wp_apply twp_eq_term.
case: tk' => //=; try by move=> *; wp_pures.
case=> [] tk' //= *; wp_pures => //.
rewrite bool_decide_decide; case: decide => [<-|ne].
- by rewrite decide_True //; wp_pures.
- by rewrite decide_False; last congruence; wp_pures.
Qed.

Lemma wp_open E t1 t2 Ψ :
  Ψ (repr (Spec.open t1 t2)) ⊢
  WP open t1 t2 @ E {{ Ψ }}.
Proof. by iIntros "?"; iApply twp_wp; iApply twp_open. Qed.

Lemma twp_enc E N k t Ψ :
  Ψ (Spec.enc N k t) ⊢
  WP enc N k t @ E [{ Ψ }].
Proof.
iIntros "post"; rewrite /enc; wp_pures.
wp_bind (tag _ _); iApply twp_tag.
by iApply twp_seal.
Qed.

Lemma wp_enc E N k t Ψ :
  Ψ (Spec.enc N k t) ⊢
  WP enc N k t @ E {{ Ψ }}.
Proof. by iIntros "?"; iApply twp_wp; iApply twp_enc. Qed.

Lemma twp_dec E N k t Ψ :
  Ψ (repr (Spec.dec N k t)) ⊢
  WP dec N k t @ E [{ Ψ }].
Proof.
iIntros "post"; rewrite /dec; wp_pures.
wp_bind (open _ _); iApply twp_open.
rewrite /Spec.dec.
case e: (Spec.open _ _) => [t'|]; wp_pures => //.
by iApply twp_untag.
Qed.

Lemma wp_dec E N k t Ψ :
  Ψ (repr (Spec.dec N k t)) ⊢
  WP dec N k t @ E {{ Ψ }}.
Proof. by iIntros "?"; iApply twp_wp; iApply twp_dec. Qed.

Lemma twp_aenc N pk t Ψ :
  Ψ (Spec.enc N pk t) ⊢
  WP aenc N pk t [{ Ψ }].
Proof. iIntros "?". wp_lam. wp_pures. by wp_apply twp_enc. Qed.

Lemma wp_aenc N pk t Ψ :
  Ψ (Spec.enc N pk t) ⊢
  WP aenc N pk t {{ Ψ }}.
Proof. iIntros "?". wp_lam. wp_pures. by wp_apply wp_enc. Qed.

Lemma twp_adec N k t Ψ :
  Ψ (repr (Spec.dec N (TKey Open k) t)) ⊢
  WP adec N k t [{ Ψ }].
Proof.
iIntros "?". wp_lam; wp_pures.
wp_apply twp_key. by wp_apply twp_dec.
Qed.

Lemma wp_adec N k t Ψ :
  Ψ (repr (Spec.dec N (TKey Open k) t)) ⊢
  WP adec N k t {{ Ψ }}.
Proof.
iIntros "?". wp_lam; wp_pures.
wp_apply wp_key. by wp_apply wp_dec.
Qed.

Lemma twp_pkey k Ψ : Ψ (TKey Seal k) ⊢ WP pkey k [{ Ψ }].
Proof. iIntros "?". wp_lam; wp_pures. by wp_apply twp_key. Qed.

Lemma wp_pkey k Ψ : Ψ (TKey Seal k) ⊢ WP pkey k {{ Ψ }}.
Proof. iIntros "?". wp_lam; wp_pures. by wp_apply wp_key. Qed.

Lemma twp_senc E N k t Ψ :
  Ψ (Spec.enc N (TKey Seal k) t) ⊢
  WP senc N k t @ E [{ Ψ }].
Proof.
iIntros "post"; rewrite /senc /Spec.enc; wp_pures.
wp_apply twp_key. by wp_apply twp_enc.
Qed.

Lemma wp_senc E N k t Ψ :
  Ψ (Spec.enc N (TKey Seal k) t) ⊢
  WP senc N k t @ E {{ Ψ }}.
Proof. by iIntros "?"; iApply twp_wp; iApply twp_senc. Qed.

Lemma twp_sdec E N k t Ψ :
  Ψ (repr (Spec.dec N (TKey Open k) t)) ⊢
  WP sdec N k t @ E [{ Ψ }].
Proof.
iIntros "post"; rewrite /sdec; wp_pures.
wp_apply twp_key. by wp_apply twp_dec.
Qed.

Lemma wp_sdec E N k t Ψ :
  Ψ (repr (Spec.dec N (TKey Open k) t)) ⊢
  WP sdec N k t @ E {{ Ψ }}.
Proof. by iIntros "?"; iApply twp_wp; iApply twp_sdec. Qed.

Lemma twp_sign N k t Ψ :
  Ψ (Spec.enc N (TKey Seal k) t) ⊢
  WP sign N k t [{ Ψ }].
Proof.
iIntros "?". wp_lam; wp_pures. wp_apply twp_key. by wp_apply twp_enc.
Qed.

Lemma wp_sign N k t Ψ :
  Ψ (Spec.enc N (TKey Seal k) t) ⊢
  WP sign N k t {{ Ψ }}.
Proof.
iIntros "?". wp_lam; wp_pures. wp_apply wp_key. by wp_apply wp_enc.
Qed.

Lemma twp_verify N k t Ψ :
  Ψ (repr (Spec.dec N k t)) ⊢
  WP verify N k t [{ Ψ }].
Proof.
iIntros "?". wp_lam; wp_pures. by wp_apply twp_dec.
Qed.

Lemma wp_verify N k t Ψ :
  Ψ (repr (Spec.dec N k t)) ⊢
  WP verify N k t {{ Ψ }}.
Proof.
iIntros "?". wp_lam; wp_pures. by wp_apply wp_dec.
Qed.

Lemma twp_vkey k Ψ : Ψ (TKey Open k) ⊢ WP vkey k [{ Ψ }].
Proof. iIntros "?". wp_lam; wp_pures. by wp_apply twp_key. Qed.

Lemma wp_vkey k Ψ : Ψ (TKey Open k) ⊢ WP vkey k {{ Ψ }}.
Proof. iIntros "?". wp_lam; wp_pures. by wp_apply wp_key. Qed.

Lemma twp_is_key E t Ψ :
  Ψ (repr (Spec.is_key t)) ⊢
  WP is_key t @ E [{ Ψ }].
Proof.
rewrite /repr /repr_option val_of_term_unseal /is_key.
iIntros "?"; by case: t=> *; wp_pures.
Qed.

Lemma wp_is_key E t Ψ :
  Ψ (repr (Spec.is_key t)) ⊢
  WP is_key t @ E {{ Ψ }}.
Proof. by iIntros "?"; iApply twp_wp; iApply twp_is_key. Qed.

Lemma wp_to_seal_key E t Ψ :
  Ψ (repr (Spec.to_seal_key t)) ⊢
  WP to_seal_key t @ E {{ Ψ }}.
Proof.
rewrite /to_seal_key; iIntros "post".
wp_pures; wp_bind (is_key _); iApply wp_is_key.
case: t => /=; try by move=> *; wp_pures => //.
case; try by move => *; wp_pures.
Qed.

Lemma wp_to_open_key E t Ψ :
  Ψ (repr (Spec.to_open_key t)) ⊢
  WP to_open_key t @ E {{ Ψ }}.
Proof.
rewrite /to_open_key; iIntros "post".
wp_pures; wp_bind (is_key _); iApply wp_is_key.
case: t => /=; try by move=> *; wp_pures => //.
case; try by move => *; wp_pures.
Qed.

End Proofs.

Arguments channel {Σ _ _} c.
