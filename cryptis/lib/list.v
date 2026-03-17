From iris.heap_lang Require Import lang notation proofmode.
From mathcomp Require ssrbool order path.
From cryptis Require Export mathcomp_compat.
From cryptis Require Import lib.repr.

Definition get_list : val := rec: "loop" "l" "n" :=
  match: "l" with NONE => NONE
  | SOME "p" =>
    if: "n" = #0 then SOME (Fst "p")
    else "loop" (Snd "p") ("n" - #1)
  end.

Notation "l !! n" := (get_list l n) : expr_scope.

Definition NILV : val := NONEV.
Definition CONSV hd tl : val := SOMEV (hd, tl).
Notation "hd :: tl" := (CONSV hd%V tl%V) : val_scope.
Notation "[ ]" := (NILV) : val_scope.
Notation "[ x ]" := (CONSV x%V NILV) : val_scope.
Notation "[ x ; y ; .. ; z ]" :=
  (CONSV x%V (CONSV y%V .. (CONSV z%V NILV) ..)) : val_scope.

Definition NIL : expr := NONE.
Definition CONS : val := λ: "hd" "tl", SOME ("hd", "tl").
Notation "hd :: tl" := (CONS hd%E tl%E) : expr_scope.
Notation "[ ]" := (NIL) : expr_scope.
Notation "[ x ]" := (CONS x%V NIL) : expr_scope.
Notation "[ x ; y ; .. ; z ]" :=
  (CONS x%E (CONS y%E .. (CONS z%E NIL) ..)) : expr_scope.

Definition eq_list : val := rec: "loop" "eq" "l1" "l2" :=
  match: "l1" with
    SOME "l1" =>
      match: "l2" with
        SOME "l2" =>
          let: "v1" := Fst "l1" in
          let: "l1" := Snd "l1" in
          let: "v2" := Fst "l2" in
          let: "l2" := Snd "l2" in
          "eq" "v1" "v2" && "loop" "eq" "l1" "l2"
      | NONE => #false
      end
   | NONE =>
     match: "l2" with
       SOME <> => #false
     | NONE => #true
     end
  end.

Definition scan_list : val := rec: "loop" "f" "l" :=
  match: "l" with
    SOME "p" =>
      let: "head" := Fst "p" in
      let: "tail" := Snd "p" in
      match: "f" "head" with
        SOME "res" => SOME "res"
      | NONE =>  "loop" "f" "tail"
      end
  | NONE => NONE
  end.

Definition find_list : val := rec: "loop" "f" "l" :=
  match: "l" with
    SOME "p" =>
      let: "head" := Fst "p" in
      let: "tail" := Snd "p" in
      if: "f" "head" then SOME "head"
      else "loop" "f" "tail"
  | NONE => NONE
  end.

Definition mem_list : val :=
  λ: "eq" "v" "l",
    match: find_list (λ: "m", "eq" "v" "m") "l" with
      SOME "r" => #true
    | NONE => #false
    end.

Definition rem_list : val := rec: "loop" "eq" "v" "l" :=
  match: "l" with
    SOME "p" =>
      let: "head" := Fst "p" in
      let: "tail" := Snd "p" in
      if: "eq" "head" "v"
      then "tail"
      else SOME ("head", "loop" "eq" "v" "tail")
  | NONE => NONE
  end.

Definition filter_list : val := rec: "loop" "f" "l" :=
  match: "l" with
    SOME "p" =>
      let: "head" := Fst "p" in
      let: "tail" := Snd "p" in
      let: "tail" := "loop" "f" "tail" in
      if: "f" "head" then SOME ("head", "tail")
      else "tail"
  | NONE => NONE
  end.

Definition append_lists : val := rec: "loop" "l1" "l2" :=
    match: "l1" with
        SOME "p" =>
            let: "head" := Fst "p" in
            let: "tail" := Snd "p" in
            SOME ("head", "loop" "tail" "l2")
      | NONE => "l2"
    end.

Definition map_list : val := rec: "loop" "f" "l" :=
    match: "l" with
        SOME "p" =>
            let: "h" := Fst "p" in
            let: "l'" := Snd "p" in
            SOME ("f" "h", "loop" "f" "l'") |
        NONE => []
    end.

Definition foldr_list : val := rec: "loop" "f" "seed" "l" :=
    match: "l" with
        SOME "p" =>
            let: "head" := Fst "p" in
            let: "tail" := Snd "p" in
            "f" "head" ("loop" "f" "seed" "tail")
        | NONE => "seed"
    end.

Definition insert_sorted : val := rec: "loop" "le" "x" "l" :=
  match: "l" with
    NONE => SOME ("x", NONE)
  | SOME "l" =>
    let: "y" := Fst "l" in
    let: "l" := Snd "l" in
    if: "le" "x" "y" then SOME ("x", SOME ("y", "l"))
    else SOME ("y", "loop" "le" "x" "l")
  end.

Definition insertion_sort : val := rec: "loop" "le" "l" :=
  match: "l" with
    NONE => NONE
  | SOME "l" =>
    let: "y" := Fst "l" in
    let: "l'" := Snd "l" in
    insert_sorted "le" "y" ("loop" "le" "l'")
  end.

Definition leq_list : val := rec: "loop" "eq" "le" "l1" "l2" :=
  match: "l1" with
    NONE => #true
  | SOME "l1" =>
    match: "l2" with
      NONE => #false
    | SOME "l2" =>
      let: "x1" := Fst "l1" in
      let: "x2" := Fst "l2" in
      let: "l1" := Snd "l1" in
      let: "l2" := Snd "l2" in
      if: "eq" "x1" "x2" then "loop" "eq" "le" "l1" "l2"
      else "le" "x1" "x2"
    end
  end.

Definition list_hd : val := λ: "l",
  match: "l" with
    NONE => NONE
  | SOME "l" => Fst "l"
  end.

Definition list_tl : val := λ: "l",
  match: "l" with
    NONE => NONE
  | SOME "l" => Snd "l"
  end.

(* Run a function until it successfully returns a value *)
Definition do_until : val := rec: "loop" "f" :=
  match: "f" #() with
    NONE => "loop" "f"
  | SOME "v" => "v"
  end.

Section ListLemmas.

Context `{!Repr A, !Repr B, !heapGS Σ}.

Implicit Types (x : A) (xs : list A).

Definition list_to_expr :=
  foldr (fun (x : A) e => CONS (repr x) e) NILV.

Lemma twp_get_list E (l : list A) (n : nat) Ψ :
  Ψ (repr (l !! n)) ⊢
  WP repr l !! #n @ E [{ Ψ }].
Proof.
rewrite /= repr_list_unseal.
elim: n l Ψ => [|n IH] [|x l] /= Ψ; iIntros "post";
wp_rec; wp_pures; eauto.
rewrite (_ : (S n - 1)%Z = n); try lia.
by iApply IH.
Qed.

Lemma wp_get_list E (l : list A) (n : nat) Ψ :
  Ψ (repr (l !! n)) ⊢
  WP repr l !! #n @ E {{ Ψ }}.
Proof. by iIntros "?"; iApply twp_wp; iApply twp_get_list. Qed.

Lemma twp_nil E Ψ :
  Ψ (repr (@nil A)) ⊢
  WP Val []%V @ E [{ Ψ }].
Proof.
by rewrite /NILV /= repr_list_unseal; iIntros "?"; wp_pures.
Qed.

Lemma wp_nil E Ψ :
  Ψ (repr (@nil A)) ⊢
  WP Val []%V @ E {{ Ψ }}.
Proof. by iIntros "?"; iApply twp_wp; iApply twp_nil. Qed.

Lemma twp_cons E x xs Ψ :
  Ψ (repr (x :: xs)) ⊢
  WP repr x :: repr xs @ E [{ Ψ }].
Proof.
rewrite /= repr_list_unseal; iIntros "post"; by rewrite /CONS; wp_pures.
Qed.

Lemma wp_cons E x xs Ψ :
  Ψ (repr (x :: xs)) ⊢
  WP repr x :: repr xs @ E {{ Ψ }}.
Proof. by iIntros "?"; iApply twp_wp; iApply twp_cons. Qed.

Lemma twp_eq_list `{EqDecision A} (f : val) (l1 l2 : list A) Φ E :
  (∀ (x1 x2 : A) Ψ,
      x1 ∈ l1 →
      Ψ #(bool_decide (x1 = x2)) -∗
      WP f (repr x1) (repr x2) @ E [{ Ψ }]) →
  Φ #(bool_decide (l1 = l2)) ⊢
  WP eq_list f (repr l1) (repr l2) @ E [{ Φ }].
Proof.
rewrite repr_list_unseal /=.
elim: l1 l2 Φ => [|x1 l1 IH] [|x2 l2] Φ wp_f /=;
iIntros "post" ; wp_rec; wp_pures; do 1?by iApply "post".
wp_bind (f _ _); iApply (wp_f x1 x2); first by set_solver.
case: (bool_decide_reflect (x1 = x2)) => [->|n_x1x2]; wp_pures; last first.
  rewrite bool_decide_decide decide_False; by [iApply "post"|congruence].
iApply IH; first by move=> *; iApply wp_f; set_solver.
case: (bool_decide_reflect (l1 = l2)) => [->|n_l1l2].
- by rewrite bool_decide_decide decide_True.
- by rewrite bool_decide_decide decide_False //; congruence.
Qed.

Lemma wp_scan_list `{Repr A} φ ψ (f : val) (l : list A) :
  □ (∀ x : A,
    {{{ ψ NONEV ∗ φ x }}}
      f (repr x)
    {{{ (r : option val), RET (repr r); ψ (repr r) }}}) -∗
  ψ NONEV ∗ ([∗ list] x ∈ l, φ x) -∗
  WP scan_list f (repr l) {{ ψ }}.
Proof.
rewrite repr_list_unseal /=.
iIntros "#wp_f"; iLöb as "IH" forall (l); iIntros "[ψ φ_l]".
wp_rec; case: l => [|h t] /=; wp_pures; first done.
iDestruct "φ_l" as "[φ_h φ_t]".
wp_apply ("wp_f" with "[$ψ $φ_h]").
iIntros "%r ψ_r"; case: r => [r|]; wp_pures; first done.
by wp_apply ("IH" with "[$]").
Qed.

Lemma wp_find_list (f : A → bool) (fimpl : val) (l : list A) E :
  (∀ x : A, {{{ True }}} fimpl (repr x) @ E {{{ RET #(f x); True }}}) →
  {{{ True }}} find_list fimpl (repr l) @ E {{{ RET (repr (find f l)); True }}}.
Proof.
rewrite repr_list_unseal /=.
iIntros "%fP"; iLöb as "IH" forall (l); iIntros "%Φ _ Hpost"; wp_rec.
case: l => [|h t] /=; wp_pures; first by iApply "Hpost".
wp_bind (fimpl _); iApply fP => //; iIntros "!> _".
case: (f h) => //; wp_pures; first by iApply "Hpost".
by iApply "IH".
Qed.

Lemma twp_find_list (f : A → bool) (fimpl : val) (l : list A) E :
  (∀ x : A, [[{ True }]] fimpl (repr x) @ E [[{ RET #(f x); True }]]) →
  [[{ True }]] find_list fimpl (repr l) @ E [[{ RET repr (find f l); True }]].
Proof.
rewrite repr_list_unseal => twp_f Φ; iIntros "_ HΦ".
iStopProof.
elim: l Φ => [| h l' IH] Φ /=; iIntros "HΦ"; wp_rec; wp_pures.
  by iApply "HΦ".
wp_apply twp_f => //; iIntros "_".
case (f h); wp_pures.
  by iApply "HΦ".
by iApply IH.
Qed.

Lemma wp_filter_list (f : A → bool) (fimpl : val) (l : list A) E :
  (∀ x : A, {{{ True }}} fimpl (repr x) @ E {{{ RET #(f x); True }}}) →
  {{{ True }}}
    filter_list fimpl (repr l) @ E
  {{{ RET (repr (List.filter f l)); True }}}.
Proof.
rewrite repr_list_unseal /=.
iIntros "%fP"; iLöb as "IH" forall (l); iIntros "%Φ _ Hpost"; wp_rec.
case: l => [|x l] /=; wp_pures; first by iApply "Hpost".
wp_bind (filter_list _ _). iApply "IH" => //. iIntros "!> _".
wp_pures. wp_bind (fimpl _); iApply fP => //; iIntros "!> _".
case f_x: (f x); wp_pures; by iApply "Hpost".
Qed.

Lemma twp_append_lists E (l1 l2 : list A) Ψ :
  Ψ (repr (l1 ++ l2)) ⊢
  WP append_lists (repr l1) (repr l2) @ E [{ Ψ }].
Proof.
rewrite repr_list_unseal.
elim: l1 Ψ => /= [| h l1' IH] Ψ; iIntros "HΨ"; wp_rec; wp_pures.
  by [].
wp_apply IH.
by wp_pures.
Qed.

Lemma twp_map_list (f : A -> B) (fimpl : val) xs E :
  Forall (λ y, [[{ True }]]
    fimpl (repr y) @ E [[{ RET repr (f y); True }]]) xs →
  [[{ True }]] map_list fimpl (repr xs) @ E [[{ RET repr (map f xs); True }]].
Proof.
  rewrite !repr_list_unseal /=.
  iIntros "%twp_fimpl_all %Φ _ HΦ"; iStopProof.
  elim: xs twp_fimpl_all Φ => [| h xs' IH] twp_fimpl_all Φ /=; iIntros "HΦ";
    wp_rec; wp_pures.
      by iApply "HΦ".
  inversion twp_fimpl_all as [| ? ? twp_fimpl twp_fimpl_rest]; subst.
  wp_apply IH => //; iIntros "_".
  wp_apply twp_fimpl => //; iIntros "_".
  wp_pures. by iApply "HΦ".
Qed.

Lemma twp_foldr_list (f : B -> A -> A) (fimpl : val) (l : list B) x E :
    (∀ (b : B) (a : A), [[{ True}]]
        fimpl (repr b) (repr a) @ E
    [[{ RET (repr (f b a)); True }]]) →
    [[{ True }]]
        foldr_list fimpl (repr x) (repr l) @ E
    [[{ RET repr (foldr f x l); True }]].
Proof.
    rewrite repr_list_unseal /=; iIntros "%twp_f %Φ _ HΦ".
    iSpecialize ("HΦ" with "[//]"); iStopProof.
    elim: l Φ => [| h l' IH] Φ /=; iIntros "HΦ";
        wp_rec; wp_pures; first done.
    wp_apply IH. wp_apply twp_f; first done; iIntros "_".
    iApply "HΦ".
Qed.

End ListLemmas.

Section ListLemmasEq.

#[warnings="-ambiguous-paths"]
Import ssrbool seq boot.eqtype.
Variable (A : eqType).
Context `{!Repr A, !heapGS Σ}.

Lemma find_if_in (v: A) (l : list A):
  v \in l = match List.find (eq_op v) l with
              Some _ => true
            | None => false
            end.
Proof.
unfold in_mem.
elim: l => [|a l IH] //=.
by case: (v == a).
Qed.

Lemma wp_mem_list (eqImpl : heap_lang.val) (v : A) (l : list A) E :
  (forall x y : A, {{{ True }}}
    eqImpl (repr x) (repr y) @ E
  {{{ RET #(eq_op x y); True }}}) ->
  {{{ True }}}
    mem_list eqImpl (repr v) (repr l) @ E
  {{{ RET #(v \in l); True }}}.
Proof.
iIntros "%H %Φ _ Hpost".
wp_lam.
wp_pures.
wp_apply (wp_find_list (eq_op v)) => //.
  iIntros "%x %Φ' _ Hpost".
  wp_pures.
  by iApply H; [| iNext].
iIntros "_". wp_pures.
rewrite find_if_in.
case: (List.find (eq_op v) l) => [a |]; wp_pures; iModIntro; by iApply "Hpost".
Qed.

Lemma twp_mem_list (eqImpl : heap_lang.val) (v : A) (l : list A) E :
  (∀ x y : A, [[{ True }]]
    eqImpl (repr x) (repr y) @ E
  [[{ RET #(eq_op x y); True }]]) →
  [[{ True }]]
    mem_list eqImpl (repr v) (repr l) @ E
  [[{ RET #(v \in l); True }]].
Proof.
iIntros "%twp_eqImpl %Φ _ HΦ".
wp_lam; wp_pures.
wp_apply twp_find_list => //.
  iIntros "%x %Ψ _ HΨ". wp_pures. wp_apply twp_eqImpl => //.
iIntros "_".
rewrite find_if_in.
case (List.find (eq_op v) l) => *; wp_pures; by iApply "HΦ".
Qed.

Lemma wp_rem_list (eqImpl : heap_lang.val) (v : A) (l : list A) E :
  (∀ x y : A, {{{ True }}}
    eqImpl (repr x) (repr y) @ E
  {{{ RET #(eq_op x y); True }}}) →
  {{{ True }}}
    rem_list eqImpl (repr v) (repr l) @ E
  {{{ RET (repr (seq.rem v l)); True }}}.
Proof.
  rewrite repr_list_unseal /=.
  iIntros "%eqP"; iLöb as "IH" forall (l); iIntros "%Φ _ Hpost".
  wp_lam. wp_pures.
  case: l => [|x l] /=; wp_pures; first by iApply "Hpost".
  wp_apply eqP => //. iIntros "_".
  case: (x == v); wp_pures; first by iApply "Hpost".
  wp_apply "IH" => //. iIntros "_".
  wp_pures. by iApply "Hpost".
Qed.

Lemma twp_rem_list (eqImpl : heap_lang.val) (v : A) (l : list A) E :
    (∀ x y : A, [[{ True }]]
        eqImpl (repr x) (repr y) @ E
    [[{ RET #(eq_op x y); True }]]) →
    [[{ True }]]
        rem_list eqImpl (repr v) (repr l) @ E
    [[{ RET repr (seq.rem v l); True }]].
Proof.
    rewrite repr_list_unseal /=.
    iIntros "%twp_eqImpl %Φ _ HΦ".
    iStopProof; elim: l Φ => [| h l' IH] Φ /=; iIntros "HΦ"; wp_rec; wp_pures;
        first by iApply "HΦ".
    wp_apply twp_eqImpl => //; iIntros "_".
    case: (h == v) => /=; wp_pures; first by iApply "HΦ".
    wp_apply IH; iIntros "_".
    wp_pures. by iApply "HΦ".
Qed.

End ListLemmasEq.

Section DoUntil.

Context `{!heapGS Σ}.

Lemma wp_do_until E (f : val) φ (Ψ : val → iProp Σ) :
  □ (φ -∗
     WP f #() @ E {{ v, ⌜v = NONEV⌝ ∗ φ ∨
                        ∃ v', ⌜v = SOMEV v'⌝ ∗ Ψ v' }}) -∗
  φ -∗
  WP do_until f @ E {{ Ψ }}.
Proof.
iIntros "#wp_f Hφ"; iLöb as "IH".
wp_rec. wp_bind (f _).
iApply (wp_wand with "[Hφ]"); first iApply "wp_f" => //.
iIntros "%v [[-> Hφ] | (%v' & -> & Hv')]"; wp_pures; eauto.
iApply ("IH" with "Hφ").
Qed.

Lemma wp_do_until' E (f : val) (φ : val → iProp Σ) :
  □ WP f #() @ E {{ v, ⌜v = NONEV⌝ ∨ (∃ v', ⌜v = SOMEV v'⌝ ∗ φ v') }} -∗
  WP do_until f @ E {{ φ }}.
Proof.
iIntros "#wp_f".
iAssert True%I as "I" => //.
iRevert "I".
iApply wp_do_until.
iIntros "!> _".
iApply wp_wand; eauto.
iIntros "%v [->|post]"; eauto.
Qed.

End DoUntil.

Section Ordered.

#[warnings="-ambiguous-paths"]
Import ssrbool seq all_order path deriving.instances.
Variable (d : Order.disp_t) (A : orderType d).
Context `{!Repr A, !heapGS Σ}.
Import Order Order.POrderTheory Order.TotalTheory.
Implicit Types (x y z : A) (s : seqlexi_with d A).

Lemma twp_insert_sorted (f : val) (x : A) (l : list A) E :
  is_true (sorted le l) →
  (∀ (y z : A),
      [[{ True }]] f (repr y) (repr z) @ E [[{ RET #(le y z); True }]]) →
  [[{ True }]]
    insert_sorted f (repr x) (repr l) @ E
  [[{ RET (repr (sort le (x :: l))); True }]].
Proof.
rewrite repr_list_unseal => sorted_l wp_f Φ; iIntros "_ post".
iSpecialize ("post" with "[//]"); iStopProof.
elim: l sorted_l Φ => //= [|y l IH] path_l Φ;
iIntros "post"; wp_rec; wp_pures => //.
move/(_ (path_sorted path_l)) in IH.
wp_bind (f _ _); iApply wp_f => //; iIntros "_".
have [le_xy|le_yx] := boolP (x <= y)%O; wp_pures.
  by rewrite sort_le_id //= ?le_xy.
move: le_yx; rewrite -ltNge => /ltW le_yx.
wp_bind (insert_sorted _ _ _); iApply IH.
suff -> : sort le [:: x, y & l] = y :: sort le (x :: l) by wp_pures.
rewrite -[RHS]sort_le_id /=.
  apply/perm_sort_leP/perm_consP.
  exists 1, (l ++ [:: x])%SEQ.
  by rewrite /= perm_catC perm_sym /= perm_sort; split.
rewrite path_min_sorted ?sort_le_sorted // all_sort /= le_yx /=.
apply: order_path_min => //; apply: le_trans.
Qed.

Lemma twp_insertion_sort (f : val) (l : list A) E :
  (∀ (x y : A),
    [[{ True }]] f (repr x) (repr y) @ E [[{ RET #(le x y); True }]]) →
  [[{ True }]]
    insertion_sort f (repr l) @ E
  [[{ RET (repr (sort le l)); True }]].
Proof.
  rewrite repr_list_unseal => wp_f Φ; iIntros "_ Hpost".
  iSpecialize ("Hpost" with "[//]"). iStopProof.
  elim: l Φ => [| y l' IH] Φ; iIntros "Hpost"; wp_rec; wp_pures.
    iApply "Hpost".
  wp_apply IH.
  rewrite -repr_list_unseal; iApply twp_insert_sorted => //; iIntros "_".
  suff ->: sort <=%O (y :: sort <=%O l') = sort <=%O (y :: l') by [].
  apply /perm_sort_leP. rewrite perm_cons.
  apply /permPl /perm_sort.
Qed.

Lemma twp_leq_list (feq : val) (fle : val) s1 s2 E :
  (∀ x1 x2,
      [[{ True }]]
        feq (repr x1) (repr x2) @ E
      [[{ RET #(eqtype.eq_op x1 x2); True }]]) →
  (∀ x1 x2,
      is_true (x1 \in s1) →
      [[{ True }]]
        fle (repr x1) (repr x2) @ E
      [[{ RET #(le x1 x2); True }]]) →
  [[{ True }]]
    leq_list feq fle (repr s1) (repr s2) @ E
  [[{ RET #(le s1 s2); True }]].
Proof.
move=> feqP fleqP Φ; iIntros "_ post".
iSpecialize ("post" with "[//]"); iStopProof.
move: fleqP; rewrite /= repr_list_unseal.
elim: s1 s2 => [|x1 s1 IH] [|x2 s2] fleP; iIntros "HΦ"; wp_rec; wp_pures => //.
rewrite lexi_cons; wp_bind (feq _ _); iApply feqP => //; iIntros "_".
case: (ltgtP x1 x2) => [l_x1x2|l_x2x1|<-] /=; wp_pures.
- by iApply fleP; rewrite ?inE ?eqtype.eqxx // ltW //; iIntros "_".
- by iApply fleP; rewrite ?inE ?eqtype.eqxx // leNgt l_x2x1 //; iIntros "_".
- iApply IH => // x1' ? x1'_in ?; iIntros "_ post".
  by iApply fleP; rewrite // inE x1'_in orbT.
Qed.

End Ordered.
