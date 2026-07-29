(** Signed multisets over a type [T] equipped with a decidable total order [R]
    and an involution [i : T -> T].  The involution's laws — that [i] is an
    involution ([i (i x) = x]) and has no fixed points ([i x <> x]) — are NOT
    assumed globally: they are taken as hypotheses on exactly the elements of the
    list each lemma operates on.  This lets [T] be a large type whose involution
    only behaves well on a sub-collection (e.g. all pre-terms, with [inv_aux] an
    involution only on the well-formed ones): to use [to X]/[wf_to X]/… one only
    needs the laws to hold on the elements of [X].

    A signed multiset is represented by a [list T].  Its "signed count" at [x] is

        count x X = count_mem x X - count_mem (i x) X   (in Z),

    so that [count (i x) X = - count x X].  A list is well-formed ([wf]) when it
    is sorted and no element occurs together with its inverse ([invs_canceled]).
    [to] normalises a list by cancelling inverse pairs and sorting; when the
    involution laws hold on the elements of [X] it is the canonical form:

      (1) [wf (to X)];
      (2) [to X = to Y <-> forall z, i (i z) = z -> count z X = count z Y].

    The [count]/[invs_canceled]/[wf]/[insert]/[cancel]/[to] *definitions* never
    mention the involution laws, so their types are independent of them; only the
    *theorems* take the per-list hypotheses. *)

From mathcomp Require Import ssreflect.
From stdpp Require Import sorting list numbers.
From Stdlib Require Import ZArith Lia.
From cryptis.lib Require Import list_sort.

Module SMS.

Section SignedMultiset.

Context {T : Type} `{EqDecision T}.
Context (R : relation T)
  `{!RelDecision R, !Transitive R, !Total R, !AntiSymm (=@{T}) R}.
Context (i : T -> T).

Implicit Types (x y z : T) (X Y : list T).

(** ** Definitions *)

Definition count x X : Z :=
  (Z.of_nat (count_mem x X) - Z.of_nat (count_mem (i x) X))%Z.

(** [invs_canceled X] : no element of [X] occurs together with its inverse. *)
Definition invs_canceled X : bool :=
  forallb (fun x => bool_decide (i x ∉ X)) X.

Definition wf X : bool :=
  bool_decide (StronglySorted R X) && invs_canceled X
  && forallb (fun x => bool_decide (i (i x) = x)) X   (* [i] involutive on elements *)
  && forallb (fun x => bool_decide (i x <> x)) X.      (* [i] fixed-point-free on them *)

(** [insert x X] adds [x] to [X], cancelling against an occurrence of [i x] if
    one is present; [cancel] cancels all inverse pairs of a list. *)
Definition insert x X : list T :=
  if bool_decide (i x ∈ X) then rem (i x) X else x :: X.

Definition cancel : list T -> list T := foldr insert [].

Definition to X : list T := merge_sort R (cancel X).

Lemma cancel_cons x X : cancel (x :: X) = insert x (cancel X).
Proof. reflexivity. Qed.

(** ** The involution (per-point laws)

    Each lemma below assumes [i (i _) = _] / [i _ <> _] only at the points it
    needs; downstream these are discharged from a [Forall]-style well-formedness
    fact on the list's elements. *)

Lemma i_inj {z x} : i (i z) = z -> i (i x) = x -> i z = i x -> z = x.
Proof. move=> iKz iKx e; by rewrite -iKz e iKx. Qed.

Lemma bool_decide_ii {z x} :
  i (i z) = z -> i (i x) = x -> bool_decide (i z = i x) = bool_decide (z = x).
Proof.
move=> iKz iKx; apply: bool_decide_ext; split.
- exact: (i_inj iKz iKx).
- by move=> ->.
Qed.

Lemma bool_decide_ix {z x} :
  i (i z) = z -> i (i x) = x -> bool_decide (i z = x) = bool_decide (z = i x).
Proof.
move=> iKz iKx; apply: bool_decide_ext; split.
- by move=> e; rewrite -iKz e.
- by move=> e; rewrite e iKx.
Qed.

(** [cancel] only shrinks the underlying set of elements. *)

Lemma mem_insert y x X : y ∈ insert x X -> y ∈ x :: X.
Proof.
rewrite /insert; case_bool_decide as Hin => yin.
- rewrite elem_of_cons; right; exact: (elem_of_rem yin).
- exact: yin.
Qed.

Lemma mem_cancel {z X} : z ∈ cancel X -> z ∈ X.
Proof.
elim: X => [H|x X IH]; first exact: H.
rewrite cancel_cons => /mem_insert /elem_of_cons [->|xin].
- by rewrite elem_of_cons; left.
- by rewrite elem_of_cons; right; exact: (IH xin).
Qed.

(** [insert]/[cancel] preserve the parity of the length (each [insert] flips it,
    and [cancel] flips it once per element); law-free. *)

Lemma parity_insert x X :
  Nat.odd (length (insert x X)) = negb (Nat.odd (length X)).
Proof.
rewrite /insert; case_bool_decide as H.
- rewrite (length_rem _ _ H).
  case: X H => [|a X'] H; first by rewrite elem_of_nil in H.
  by rewrite /= Nat.sub_0_r Nat.odd_succ Nat.negb_even.
- by rewrite /= Nat.odd_succ -Nat.negb_odd.
Qed.

Lemma parity_cancel X : Nat.odd (length (cancel X)) = Nat.odd (length X).
Proof.
elim: X => [//|x X IH].
by rewrite cancel_cons parity_insert IH Nat.odd_succ Nat.negb_odd.
Qed.

Lemma parity_to X : Nat.odd (length (to X)) = Nat.odd (length X).
Proof. by rewrite /to (length_merge_sort R (cancel X)) parity_cancel. Qed.

(** ** Signed counts *)

Instance count_proper z : Proper ((≡ₚ) ==> (=)) (count z).
Proof.
move=> X Y e; rewrite /count.
by rewrite (count_mem_Permutation z X Y e) (count_mem_Permutation (i z) X Y e).
Qed.

Lemma count_cons z x X :
  count z (x :: X) =
  (count z X + Z.b2z (bool_decide (z = x))
             - Z.b2z (bool_decide (i z = x)))%Z.
Proof. rewrite /count /=; case_bool_decide; case_bool_decide; simpl; lia. Qed.

Lemma count_app z X Y : count z (X ++ Y) = (count z X + count z Y)%Z.
Proof. rewrite /count !count_mem_app !Nat2Z.inj_add; lia. Qed.

(** Cancelling one [i x] against [x] leaves every signed count unchanged:
    [insert] behaves like consing as far as [count] is concerned.  Needs the
    involution at the query point [z] and at the inserted point [x]. *)

Lemma count_insert z x X :
  i (i z) = z -> i (i x) = x -> count z (insert x X) = count z (x :: X).
Proof.
move=> iKz iKx; rewrite /insert; case_bool_decide as Hin; last done.
have e : count z X = count z (i x :: rem (i x) X).
  by rewrite -rem_Permutation.
rewrite (count_cons z (i x) (rem (i x) X)) in e.
rewrite (count_cons z x X) (bool_decide_ii iKz iKx) in e *.
rewrite (bool_decide_ix iKz iKx); lia.
Qed.

Lemma count_cancel z X :
  i (i z) = z -> (forall x, x ∈ X -> i (i x) = x) ->
  count z (cancel X) = count z X.
Proof.
move=> iKz; elim: X => [|x X IH]; first done.
move=> H.
have iKx : i (i x) = x by apply: H; rewrite elem_of_cons; by left.
have iKX : forall y, y ∈ X -> i (i y) = y
  by move=> y yX; apply: H; rewrite elem_of_cons; by right.
by rewrite cancel_cons (count_insert z x (cancel X) iKz iKx)
           (count_cons z x (cancel X)) (count_cons z x X) (IH iKX).
Qed.

Lemma count_to z X :
  i (i z) = z -> (forall x, x ∈ X -> i (i x) = x) ->
  count z (to X) = count z X.
Proof.
move=> iKz iKX.
by rewrite /to merge_sort_Permutation count_cancel.
Qed.

(** ** Cancellation removes all inverse pairs *)

Lemma invs_canceledP X : invs_canceled X <-> (forall x, x ∈ X -> i x ∉ X).
Proof.
rewrite /invs_canceled forallb_True list.Forall_forall; split => H x xX; move: (H x xX).
- exact: bool_decide_unpack.
- exact: bool_decide_pack.
Qed.

Instance invs_canceled_proper : Proper ((≡ₚ) ==> (=)) invs_canceled.
Proof.
move=> X Y e; apply: eq_bool_prop_intro.
rewrite !invs_canceledP; split => H x.
- rewrite -e; exact: (H x).
- rewrite e; exact: (H x).
Qed.

Lemma invs_canceled_insert x X :
  i x <> x -> (forall y, y ∈ X -> i (i y) = y) ->
  invs_canceled X -> invs_canceled (insert x X).
Proof.
move=> iNx iKX; rewrite !invs_canceledP => H y.
rewrite /insert; case_bool_decide as Hin.
- move=> yin iyin.
  exact: (H y (elem_of_rem yin) (elem_of_rem iyin)).
- rewrite elem_of_cons => -[-> | yX].
  + rewrite elem_of_cons => -[ixx | ixX].
    * exact: (iNx ixx).
    * exact: (Hin ixX).
  + rewrite elem_of_cons => -[iyx | iyX].
    * apply: Hin.
      have -> : i x = y by rewrite -iyx (iKX y yX).
      exact: yX.
    * exact: (H y yX iyX).
Qed.

Lemma invs_canceled_cancel X :
  (forall x, x ∈ X -> i x <> x) -> (forall x, x ∈ X -> i (i x) = x) ->
  invs_canceled (cancel X).
Proof.
elim: X => [_ _|x X IH iNX iKX].
- by rewrite /invs_canceled /cancel /=.
- rewrite cancel_cons.
  apply: (invs_canceled_insert x (cancel X)).
  + apply: iNX; rewrite elem_of_cons; by left.
  + move=> y /mem_cancel yin; apply: iKX; rewrite elem_of_cons; by right.
  + apply: IH.
    * move=> y yX; apply: iNX; rewrite elem_of_cons; by right.
    * move=> y yX; apply: iKX; rewrite elem_of_cons; by right.
Qed.

(** A list with no inverse pairs is a fixed point of [cancel]; law-free. *)
Lemma cancel_id {X} : invs_canceled X -> cancel X = X.
Proof.
elim: X => [//|x X IH] HC.
move: (HC) => /invs_canceledP H.
have HX : invs_canceled X.
{ apply/invs_canceledP => y yX.
  have Hy : i y ∉ x :: X by apply: H; rewrite elem_of_cons; by right.
  move: Hy; rewrite not_elem_of_cons; by case. }
have Hx : i x ∉ X.
{ have Hx' : i x ∉ x :: X by apply: H; rewrite elem_of_cons; by left.
  move: Hx'; rewrite not_elem_of_cons; by case. }
by rewrite cancel_cons (IH HX) /insert (bool_decide_eq_false_2 _ Hx).
Qed.

(** If [invs_canceled X], the plain multiplicity is recovered from the
    signed count.  (Needs no involution law.) *)
Lemma count_mem_of_invs_canceled z X :
  invs_canceled X -> Z.of_nat (count_mem z X) = Z.max 0 (count z X).
Proof.
move=> /invs_canceledP H; rewrite /count.
case: (decide (z ∈ X)) => zX.
- rewrite (proj1 (not_elem_of_count_mem (i z) X) (H z zX)); lia.
- rewrite (proj1 (not_elem_of_count_mem z X) zX); lia.
Qed.

(** ** Well-formedness: reflection, extraction, introduction

    The two involution conjuncts of [wf] are reflected pointwise, so a single
    [wf X] fact certifies (besides sortedness and cancellation) that [i] is an
    involution and fixed-point-free on the *elements of [X]* — exactly the
    per-list hypotheses the other lemmas take, now carried by [wf] itself. *)

Lemma wf_involP X :
  forallb (fun x => bool_decide (i (i x) = x)) X <-> (forall x, x ∈ X -> i (i x) = x).
Proof.
rewrite forallb_True list.Forall_forall; split => H x xX; move: (H x xX).
- exact: bool_decide_unpack.
- exact: bool_decide_pack.
Qed.

Lemma wf_fpfP X :
  forallb (fun x => bool_decide (i x <> x)) X <-> (forall x, x ∈ X -> i x <> x).
Proof.
rewrite forallb_True list.Forall_forall; split => H x xX; move: (H x xX).
- exact: bool_decide_unpack.
- exact: bool_decide_pack.
Qed.

Lemma wf_sorted X : wf X -> StronglySorted R X.
Proof. move=> /andb_True [/andb_True [/andb_True [HS _] _] _]; exact: bool_decide_unpack HS. Qed.

Lemma wf_invs_canceled X : wf X -> invs_canceled X.
Proof. by move=> /andb_True [/andb_True [/andb_True [_ ?] _] _]. Qed.

Lemma wf_invol X : wf X -> forall x, x ∈ X -> i (i x) = x.
Proof. move=> /andb_True [/andb_True [_ Hinvol] _]; by apply/wf_involP. Qed.

Lemma wf_fpf X : wf X -> forall x, x ∈ X -> i x <> x.
Proof. move=> /andb_True [_ Hfpf]; by apply/wf_fpfP. Qed.

Lemma wf_intro X :
  StronglySorted R X -> (forall x, x ∈ X -> i x ∉ X) ->
  (forall x, x ∈ X -> i (i x) = x) -> (forall x, x ∈ X -> i x <> x) ->
  wf X.
Proof.
move=> HS Hic Hinvol Hfpf; apply/andb_True; split; last first.
{ by apply/wf_fpfP. }
apply/andb_True; split; last first.
{ by apply/wf_involP. }
apply/andb_True; split.
- by apply: bool_decide_pack.
- by apply/invs_canceledP.
Qed.

Lemma wf_nil : wf [].
Proof.
apply: wf_intro.
- constructor.
- move=> x Hx; exact: not_elem_of_nil.
- move=> x Hx; exfalso; exact: not_elem_of_nil Hx.
- move=> x Hx; exfalso; exact: not_elem_of_nil Hx.
Qed.

Lemma wf_singleton x : i x <> x -> i (i x) = x -> wf [x].
Proof.
move=> iNx iKx; apply: wf_intro.
- by repeat constructor.
- move=> y /list_elem_of_singleton ->; rewrite list_elem_of_singleton; exact: iNx.
- by move=> y /list_elem_of_singleton ->.
- by move=> y /list_elem_of_singleton ->.
Qed.

(** ** Main results *)

Lemma wf_to X :
  (forall x, x ∈ X -> i x <> x) -> (forall x, x ∈ X -> i (i x) = x) ->
  wf (to X).
Proof.
move=> iNX iKX.
have memX : forall x, x ∈ to X -> x ∈ X.
  move=> x; rewrite /to => xin; apply: mem_cancel.
  by rewrite -(merge_sort_Permutation R (cancel X)).
apply: wf_intro.
- rewrite /to; exact: merge_sort_sorted.
- apply/invs_canceledP; rewrite /to merge_sort_Permutation.
  exact: (invs_canceled_cancel X iNX iKX).
- move=> x /memX xX; exact: iKX.
- move=> x /memX xX; exact: iNX.
Qed.

(** A well-formed list is a fixed point of [to]; law-free.  This is the exposed
    form (over [to]) of [cancel_id] + [merge_sort_id]. *)
Lemma to_id X : wf X -> to X = X.
Proof.
move=> /andb_True [/andb_True [/andb_True [/bool_decide_unpack Hs Hc] _] _].
by rewrite /to (cancel_id Hc) (merge_sort_id R X Hs).
Qed.

Lemma to_eq X Y :
  (forall x, x ∈ X -> i x <> x) -> (forall x, x ∈ X -> i (i x) = x) ->
  (forall x, x ∈ Y -> i x <> x) -> (forall x, x ∈ Y -> i (i x) = x) ->
  (to X = to Y <-> (forall z, i (i z) = z -> count z X = count z Y)).
Proof.
move=> iNX iKX iNY iKY; split.
- move=> e z iKz.
  by rewrite -(count_to z X iKz iKX) -(count_to z Y iKz iKY) e.
- move=> Hc; rewrite /to.
  apply: merge_sort_Permutation_eq; apply: Permutation_count_mem => z.
  apply: Nat2Z.inj.
  case: (decide (z ∈ cancel X)) => zX.
  + have iKz : i (i z) = z := iKX z (mem_cancel zX).
    rewrite (count_mem_of_invs_canceled z (cancel X) (invs_canceled_cancel X iNX iKX)).
    rewrite (count_mem_of_invs_canceled z (cancel Y) (invs_canceled_cancel Y iNY iKY)).
    by rewrite (count_cancel z X iKz iKX) (count_cancel z Y iKz iKY) (Hc z iKz).
  + case: (decide (z ∈ cancel Y)) => zY.
    * have iKz : i (i z) = z := iKY z (mem_cancel zY).
      rewrite (count_mem_of_invs_canceled z (cancel X) (invs_canceled_cancel X iNX iKX)).
      rewrite (count_mem_of_invs_canceled z (cancel Y) (invs_canceled_cancel Y iNY iKY)).
      by rewrite (count_cancel z X iKz iKX) (count_cancel z Y iKz iKY) (Hc z iKz).
    * by rewrite (proj1 (not_elem_of_count_mem z (cancel X)) zX)
                 (proj1 (not_elem_of_count_mem z (cancel Y)) zY).
Qed.

(** [cancel] respects the signed counts up to permutation — [to_eq] read through
    [merge_sort] being a permutation. *)
Lemma cancel_Permutation X Y :
  (forall x, x ∈ X -> i x <> x) -> (forall x, x ∈ X -> i (i x) = x) ->
  (forall x, x ∈ Y -> i x <> x) -> (forall x, x ∈ Y -> i (i x) = x) ->
  (forall z, i (i z) = z -> count z X = count z Y) -> cancel X ≡ₚ cancel Y.
Proof.
move=> iNX iKX iNY iKY Hc.
rewrite -(merge_sort_Permutation R (cancel X)) -(merge_sort_Permutation R (cancel Y)).
by rewrite -/(to X) -/(to Y) (proj2 (to_eq X Y iNX iKX iNY iKY) Hc).
Qed.

(** [to] only shrinks the underlying set of elements (via [cancel]). *)
Lemma mem_to z X : z ∈ to X -> z ∈ X.
Proof. rewrite /to => zin; apply: mem_cancel; by rewrite -(merge_sort_Permutation R (cancel X)). Qed.

(** A well-formed singleton is a fixed point of [to]. *)
Lemma to_singleton x : i x <> x -> i (i x) = x -> to [x] = [x].
Proof. move=> iNx iKx; apply: to_id; exact: wf_singleton. Qed.

(** [to] is a genuine (Leibniz) function of the underlying signed multiset:
    permutation-equal inputs give *equal* canonical forms. *)
Lemma to_Permutation X Y :
  (forall x, x ∈ X -> i x <> x) -> (forall x, x ∈ X -> i (i x) = x) ->
  (forall x, x ∈ Y -> i x <> x) -> (forall x, x ∈ Y -> i (i x) = x) ->
  X ≡ₚ Y -> to X = to Y.
Proof.
move=> iNX iKX iNY iKY e.
apply: (proj2 (to_eq X Y iNX iKX iNY iKY)) => z iKz.
by rewrite e.
Qed.

(** Canonicalising a suffix before concatenating does not change the canonical
    form of the whole: [to] absorbs an inner [to]. *)
Lemma to_cat_to A B :
  (forall x, x ∈ A -> i x <> x) -> (forall x, x ∈ A -> i (i x) = x) ->
  (forall x, x ∈ B -> i x <> x) -> (forall x, x ∈ B -> i (i x) = x) ->
  to (A ++ to B) = to (A ++ B).
Proof.
move=> iNA iKA iNB iKB.
have memB : forall x, x ∈ to B -> x ∈ B by move=> x; exact: mem_to.
have lawN : forall x, x ∈ A ++ to B -> i x <> x.
  move=> x; rewrite elem_of_app => - [xA|xtoB]; [exact: iNA | exact: (iNB _ (memB _ xtoB))].
have lawK : forall x, x ∈ A ++ to B -> i (i x) = x.
  move=> x; rewrite elem_of_app => - [xA|xtoB]; [exact: iKA | exact: (iKB _ (memB _ xtoB))].
have lawN' : forall x, x ∈ A ++ B -> i x <> x.
  move=> x; rewrite elem_of_app => - [xA|xB]; [exact: iNA | exact: iNB].
have lawK' : forall x, x ∈ A ++ B -> i (i x) = x.
  move=> x; rewrite elem_of_app => - [xA|xB]; [exact: iKA | exact: iKB].
apply: (proj2 (to_eq _ _ lawN lawK lawN' lawK')) => z iKz.
by rewrite !count_app (count_to z B iKz iKB).
Qed.

(** Left-cancellation of a common prefix under [to]: since [to] is determined by
    the signed counts, a shared prefix [A] can be cancelled. *)
Lemma to_app_cancel_l A X Y :
  (forall x, x ∈ A -> i x <> x) -> (forall x, x ∈ A -> i (i x) = x) ->
  (forall x, x ∈ X -> i x <> x) -> (forall x, x ∈ X -> i (i x) = x) ->
  (forall x, x ∈ Y -> i x <> x) -> (forall x, x ∈ Y -> i (i x) = x) ->
  to (A ++ X) = to (A ++ Y) -> to X = to Y.
Proof.
move=> iNA iKA iNX iKX iNY iKY e.
have lawN : forall Z, (forall x, x ∈ Z -> i x <> x) ->
              forall x, x ∈ A ++ Z -> i x <> x.
  move=> Z hZ x; rewrite elem_of_app => -[?|?]; by [apply: iNA|apply: hZ].
have lawK : forall Z, (forall x, x ∈ Z -> i (i x) = x) ->
              forall x, x ∈ A ++ Z -> i (i x) = x.
  move=> Z hZ x; rewrite elem_of_app => -[?|?]; by [apply: iKA|apply: hZ].
apply: (proj2 (to_eq X Y iNX iKX iNY iKY)) => z iKz.
have := proj1 (to_eq (A ++ X) (A ++ Y) (lawN _ iNX) (lawK _ iKX)
                     (lawN _ iNY) (lawK _ iKY)) e z iKz.
rewrite !count_app; lia.
Qed.

End SignedMultiset.

End SMS.

Global Existing Instance SMS.count_proper.
Global Existing Instance SMS.invs_canceled_proper.
