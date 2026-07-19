From cryptis Require Import mathcomp_compat lib.
From mathcomp Require Import ssreflect.
From mathcomp Require eqtype ssrbool path.
From deriving Require Import deriving.
From stdpp Require Import gmap.
From iris.heap_lang Require Import notation.
From iris.heap_lang Require Import primitive_laws.
From cryptis.core.term Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*
Lemma tsize_TExpN_exp t ts t' : t' ∈ ts → tsize t' < tsize (TExpN t ts).
Proof.
elim: ts => [|t'' ts IH].
- by rewrite elem_of_nil.
- rewrite elem_of_cons; case => [->|/IH t'_ts].
  + by case: (tsize_TExpN_lt t ts t'').
  + case: (tsize_TExpN_lt t ts t'') => ??; lia.
Qed.
*)

(*
Lemma tsize_TExp_exp t1 t2 : tsize t2 < tsize (TExp t1 t2).
Proof. apply: tsize_TExpN_exp. rewrite elem_of_cons. by auto. Qed.
*)

Canonical termO := leibnizO term.

(* Universal on wf lists: products pass through [cancel_invs] untouched and atoms
   cancel by count, both permutation-stable (see [PreTerm.perm_cancel_invs_wf]).
   [cancel_invs] only ever feeds [map unfold_term _], which is always wf. *)
Global Instance cancel_invs_proper : Proper ((≡ₚ) ==> (≡ₚ)) cancel_invs.
Proof.
move=> ts1 ts2 H12.
have peq : is_true (seq.perm_eq ts1 ts2) := ssrbool.introT perm_Perm H12.
apply: (ssrbool.elimT perm_Perm).
rewrite /cancel_invs; apply: seq.perm_map.
apply: PreTerm.perm_cancel_invs_wf; first exact: wf_unfold_terms.
exact: seq.perm_map.
Qed.

Global Instance TExpN_proper : Proper ((=) ==> (≡ₚ) ==> (=)) TExpN.
Proof.
move=> t _ <- ts1 ts2 ts12.
by apply/TExpN_perm/(ssrbool.introT perm_Perm).
Qed.

Lemma TExpC2 g t1 t2 : TExpN g [t1; t2] = TExpN g [t2; t1].
Proof. by rewrite Permutation_swap. Qed.

Global Instance term_inhabited : Inhabited term.
Proof. exact: (populate (TInt 0)). Qed.

Global Instance aenc_key_inhabited : Inhabited aenc_key :=
  populate (AEncKey inhabitant).

Global Instance sign_key_inhabited : Inhabited sign_key :=
  populate (SignKey inhabitant).

Global Instance senc_key_inhabited : Inhabited senc_key :=
  populate (SEncKey inhabitant).

Definition term_eq_dec : EqDecision term :=
  Eval hnf in def_eq_decision _.
Global Existing Instance term_eq_dec.

Definition aenc_key_eq_dec : EqDecision aenc_key :=
  Eval hnf in def_eq_decision _.
Global Existing Instance aenc_key_eq_dec.

Definition senc_key_eq_dec : EqDecision senc_key :=
  Eval hnf in def_eq_decision _.
Global Existing Instance senc_key_eq_dec.

Definition sign_key_eq_dec : EqDecision sign_key :=
  Eval hnf in def_eq_decision _.
Global Existing Instance sign_key_eq_dec.

Lemma subseteq_cancel_invs ts : cancel_invs ts ⊆ ts.
Proof. by move => ? /(ssrbool.introT inP) /mem_cancel_invs /(ssrbool.elimT inP). Qed.
Global Arguments subseteq_cancel_invs ts : clear implicits.

Lemma tsize_lt_TExp t1 t2 :
  negb (is_mul t2) ->
  TInv t2 ∉ exps t1 ->
  tsize t1 < tsize (TExp t1 t2) /\
  tsize (TInv t2) < tsize (TExp t1 t2) /\
  tsize t2 < tsize (TExp t1 t2).
Proof.
move => /is_trueP Nm2 /(ssrbool.introN inP) t2_t1.
move: (@tsize_lt_TExp t1 t2 Nm2 t2_t1) => [h1 [h2 h3]].
by split; [|split]; apply/(ssrbool.elimT ssrnat.leP).
Qed.

Lemma tsize_TExp_TInv t1 t2 :
  negb (is_mul (TInv t2)) ->
  t2 ∈ exps t1 ->
  tsize t2 < tsize t1 /\
  tsize (TInv t2) < tsize t1 /\
  tsize (TExp t1 (TInv t2)) < tsize t1.
Proof.
move => /is_trueP NmI2 /(ssrbool.introT inP) t2_t1.
move: (@tsize_TExp_TInv t1 t2 NmI2 t2_t1) => [h1 [h2 h3]].
by split; [|split]; apply/(ssrbool.elimT ssrnat.leP).
Qed.

Lemma TInv_neq {t} : negb (is_mul t) -> TInv t ≠ t.
Proof.
move=> /is_trueP Nm /(ssrbool.introT eqtype.eqP) /is_trueP.
by rewrite (ssrbool.negbTE (TInv_Nid Nm)).
Qed.

Lemma elem_of_TInv_exps t1 t2 : t1 ∈ exps t2 → TInv t1 ∉ exps t2.
Proof. by move => /(ssrbool.introT inP) /in_TInv_exps /(ssrbool.elimN inP). Qed.

Lemma elem_of_TInv_exps' t1 t2 : TInv t1 ∈ exps t2 → t1 ∉ exps t2.
Proof. by move => ? /elem_of_TInv_exps. Qed.

Lemma count_exp_nat_eq0 t1 t2 : t1 ∉ exps t2 → count_exp_nat t1 t2 = 0.
Proof. move => ?. exact /count_exp_nat_eq0 /(ssrbool.introN inP). Qed.

Lemma count_exp_nat_gt0 t1 t2 : (count_exp_nat t1 t2 > 0) ↔ (t1 ∈ exps t2).
Proof. by rewrite (ssrbool.rwP inP) -count_exp_nat_gt0 -(ssrbool.rwP ssrnat.leP). Qed.

Definition count_exp t ts : Z :=
  (count_exp_nat t ts - count_exp_nat (TInv t) ts)%Z.

Lemma count_exp_eq0 t1 t2 :
  t1 ∉ exps t2 → TInv t1 ∉ exps t2 → count_exp t1 t2 = 0.
Proof. by move=> ??; rewrite /count_exp !count_exp_nat_eq0. Qed.

Lemma count_exp_gt0 t1 t2 : (count_exp t1 t2 > 0)%Z ↔ t1 ∈ exps t2.
Proof.
rewrite /count_exp; case: (decide (t1 ∈ exps t2)) => t1_t2.
  rewrite [count_exp_nat (TInv _) _]count_exp_nat_eq0; last first.
    exact: elem_of_TInv_exps.
  rewrite -count_exp_nat_gt0; lia.
rewrite count_exp_nat_eq0 //; split; first lia.
by case/t1_t2.
Qed.

Lemma count_exp_TInv t ts : count_exp (TInv t) ts = Z.opp (count_exp t ts).
Proof. rewrite /count_exp TInvK. lia. Qed.

Lemma count_exp_TExp_eq t1 t2 :
  negb (is_mul t1) ->
  count_exp t1 (TExp t2 t1) = (count_exp t1 t2 + 1)%Z.
Proof.
move => Nm1.
rewrite /count_exp !(count_exp_nat_TExp _ _ _ (proj2 (is_trueP _) Nm1)) !eqtype.eqxx ssrnat.subnE.
rewrite eqtype.eq_sym (ssrbool.negbTE (TInv_Nid (proj2 (is_trueP _) Nm1))).
case: inP => H /=.
- rewrite count_exp_nat_eq0; last exact: elem_of_TInv_exps'.
  rewrite -count_exp_nat_gt0 in H; lia.
- rewrite [count_exp_nat (TInv t1) t2]count_exp_nat_eq0 //; lia.
Qed.

Lemma count_exp_TExp_TInv t1 t2 :
  negb (is_mul (TInv t1)) ->
  count_exp t1 (TExp t2 (TInv t1)) = (count_exp t1 t2 - 1)%Z.
Proof.
move => NmI1.
rewrite -{1}[t1]TInvK count_exp_TInv (count_exp_TExp_eq _ NmI1) count_exp_TInv.
lia.
Qed.

Lemma count_exp_TInv_TExp t1 t2 :
  negb (is_mul t1) ->
  count_exp (TInv t1) (TExp t2 t1) = (count_exp (TInv t1) t2 - 1)%Z.
Proof.
move => Nm1.
have h : negb (is_mul (TInv (TInv t1))) by rewrite TInvK.
by rewrite -{2}[t1]TInvK (count_exp_TExp_TInv _ h).
Qed.

Lemma count_exp_TExp_ne t1 t2 t3 :
  negb (is_mul t3) ->
  t1 ≠ t3 → t1 ≠ TInv t3 → count_exp t1 (TExp t2 t3) = count_exp t1 t2.
Proof.
move=> Nm3 t1_t3 t1_t3V.
rewrite /count_exp !(count_exp_nat_TExp _ _ _ (proj2 (is_trueP _) Nm3)).
rewrite -!eq_op_bool_decide ssrnat.subnE !bool_decide_decide.
rewrite decide_False // decide_False // decide_False; last first.
  move=> /TInv_inj; congruence.
by rewrite decide_False // => e; apply: t1_t3V; rewrite -e TInvK.
Qed.

Lemma count_exp_TExp t1 t2 t3 :
  negb (is_mul t3) ->
  count_exp t1 (TExp t2 t3) =
  if decide (t1 = t3) then
    (count_exp t1 t2 + 1)%Z
  else if decide (t1 = TInv t3) then
    (count_exp t1 t2 - 1)%Z
  else count_exp t1 t2.
Proof.
move => Nm3.
case: decide => [->|?]; first by rewrite count_exp_TExp_eq.
case: decide => [->|?]; first by rewrite count_exp_TInv_TExp.
by rewrite count_exp_TExp_ne.
Qed.

Lemma count_exp_TExpW t1 t2 t3 :
  negb (is_mul t3) ->
  t1 ≠ TInv t3 →
  (count_exp t1 t2 ≤ count_exp t1 (TExp t2 t3))%Z.
Proof.
move=> Nm3 t1_t3; rewrite count_exp_TExp // (@decide_False _ (t1 = TInv t3)) //.
by case: decide => ?; lia.
Qed.

Lemma not_elem_of_TInv_exps t1 t2 :
  negb (is_mul t1) ->
  TInv t1 ∉ exps t2 ↔ t1 ∈ exps (TExp t2 t1).
Proof.
move => Nm1.
rewrite -!count_exp_gt0 count_exp_TInv count_exp_TExp_eq //; lia.
Qed.

Lemma TExpN_appC t ts1 ts2 : TExpN t (ts1 ++ ts2) = TExpN t (ts2 ++ ts1).
Proof. exact: TExpN_catC. Qed.

Inductive subterm (t : term) : term → Prop :=
| STRefl : subterm t t
| STPair1 t1 t2 of subterm t t1 : subterm t (TPair t1 t2)
| STPair2 t1 t2 of subterm t t2 : subterm t (TPair t1 t2)
| STKey kt t' of subterm t t' : subterm t (TKey kt t')
| STSeal1 k t' of subterm t k : subterm t (TSeal k t')
| STSeal2 k t' of subterm t t' : subterm t (TSeal k t')
| STHash t' of subterm t t' : subterm t (THash t')
| STInv t' of negb (is_mul t') & negb (is_inv t') & subterm t t' : subterm t (TInv t')
| STExp1 t' ts of negb (is_exp t') & subterm t t' : subterm t (TExpN t' ts)
| STExp2 t' t'' ts of
    negb (is_exp t') &
    atomic ts &
    invs_canceled ts &
    subterm t t'' &
    t'' ∈ ts
  : subterm t (TExpN t' ts)
| STMul t'' ts of
    wf_mul_list ts &
    subterm t t'' &
    t'' ∈ ts
  : subterm t (TMulN ts).

Global Instance subterm_trans : Transitive subterm.
Proof.
move=> t1 t2 t3 sub12 sub13; elim: t3 / sub13;
by eauto using subterm.
Qed.

Section ValOfTerm.

Fixpoint val_of_term_rec t : val :=
  match t with
  | TInt n =>
    (#TOp0_tag, (#TInt_tag, #n))
  | TPair t1 t2 =>
    (#TOp2_tag, (#TPair_tag, val_of_term_rec t1, val_of_term_rec t2))%V
  | TNonce l =>
    (#TOp0_tag, (#TNonce_tag, #(nonce_loc l)))%V
  | TKey kt t =>
    (#TOp1_tag, ((#TKey_tag, repr kt), val_of_term_rec t))%V
  | TSeal t1 t2 =>
    (#TOp2_tag, (#TSeal_tag, val_of_term_rec t1, val_of_term_rec t2))%V
  | THash t =>
    (#TOp1_tag, ((#THash_tag, #()), val_of_term_rec t))%V
  | TNonFree pt _ _ => val_of_pre_term pt
  end.

Definition val_of_term_aux : seal val_of_term_rec. by eexists. Qed.
Definition val_of_term : term -> val := unseal val_of_term_aux.
Lemma val_of_term_unseal : val_of_term = val_of_term_rec.
Proof. exact: seal_eq. Qed.
Coercion val_of_term : term >-> val.
Global Instance repr_term : Repr term := val_of_term.

Global Instance repr_aenc_key : Repr aenc_key := λ k, repr (k : term).
Global Instance repr_senc_key : Repr senc_key := λ k, repr (k : term).
Global Instance repr_sign_key : Repr sign_key := λ k, repr (k : term).

Lemma val_of_pre_term_unfold t :
  val_of_pre_term (unfold_term t) = val_of_term t.
Proof.
rewrite val_of_term_unseal.
elim/term_ind': t => //=; try by move=> *; congruence.
Qed.

End ValOfTerm.

Global Instance val_of_term_inj : Inj (=) (=) val_of_term.
Proof.
move=> t1 t2 e_t1t2; apply: unfold_term_inj.
apply: val_of_pre_term_inj.
by rewrite !val_of_pre_term_unfold.
Qed.

Global Instance countable_term : Countable term.
Proof. exact: def_countable. Qed.

Global Instance countable_aenc_key : Countable aenc_key.
Proof. exact: def_countable. Qed.

Global Instance countable_sign_key : Countable sign_key.
Proof. exact: def_countable. Qed.

Global Instance countable_senc_key : Countable senc_key.
Proof. exact: def_countable. Qed.

Global Instance infinite_term : Infinite term.
Proof.
pose int_of_term (t : term) :=
  if t is TInt n then Some n else None.
apply (inj_infinite TInt int_of_term).
by move=> n; rewrite /int_of_term.
Qed.

Definition term_height t :=
  PreTerm.height (unfold_term t).

Definition nonces_of_term_def (t : term) :=
  nonces_of_pre_term (unfold_term t).
Arguments nonces_of_term_def /.
Definition nonces_of_term_aux : seal nonces_of_term_def. by eexists. Qed.
Definition nonces_of_term := unseal nonces_of_term_aux.
Lemma nonces_of_term_unseal : nonces_of_term = nonces_of_term_def.
Proof. exact: seal_eq. Qed.

Lemma nonces_of_termE' t :
  nonces_of_term t =
  match t with
  | TInt _ => ∅
  | TPair t1 t2 => nonces_of_term t1 ∪ nonces_of_term t2
  | TNonce l => {[l]}
  | TKey _ t => nonces_of_term t
  | TSeal t1 t2 => nonces_of_term t1 ∪ nonces_of_term t2
  | THash t => nonces_of_term t
  | TNonFree pt _ _ => nonces_of_pre_term pt
  end.
Proof.
by rewrite nonces_of_term_unseal; case: t => //=.
Qed.

Lemma nonces_of_term_fold pt :
  is_true (PreTerm.wf_term pt) -> nonces_of_term (fold_term pt) = nonces_of_pre_term pt.
Proof. move => wf. by rewrite nonces_of_term_unseal /nonces_of_term_def (@fold_termK pt wf). Qed.

Lemma nonces_of_pre_term_factors e :
  nonces_of_pre_term e = ⋃ map nonces_of_pre_term (PreTerm.factors e).
Proof. by case: e => [o|o1 e1|o2 e1 e2|es] //=; rewrite union_empty_r_L. Qed.

Lemma nonces_of_pre_term_inv_aux x :
  nonces_of_pre_term (PreTerm.inv_aux x) = nonces_of_pre_term x.
Proof. by case: x => [o|[kt||] e|o e1 e2|es] //=. Qed.

(* [inv] distributes [inv] over the factors and re-multiplies; [inv] preserves
   nonces, and (for wf [pt]) no cancellation occurs, so nonces are preserved. *)
Lemma nonces_of_pre_term_inv pt :
  is_true (PreTerm.wf_term pt) ->
  nonces_of_pre_term (PreTerm.inv pt) = nonces_of_pre_term pt.
Proof.
move => wf.
rewrite (PreTerm.inv_factors wf) (nonces_of_pre_term_factors pt).
set F := PreTerm.factors pt.
have wfF : is_true (seq.all PreTerm.wf_term F) := PreTerm.wf_factors wf.
have NmF : is_true (seq.all (fun t => negb (PreTerm.is_mul t)) F) := PreTerm.Nmul_factors wf.
have cancF : is_true (PreTerm.invs_canceled F) := PreTerm.invs_canceled_factors wf.
have wfMI : is_true (seq.all PreTerm.wf_term (seq.map PreTerm.inv_aux F)).
  apply: (ssrbool.introT seq.allP) => x /(ssrbool.elimT seq.mapP) [y yF ->].
  by apply: PreTerm.wf_inv_aux; [exact: (ssrbool.elimT seq.allP wfF _ yF)|exact: (ssrbool.elimT seq.allP NmF _ yF)].
have NmMI : is_true (seq.all (fun t => negb (PreTerm.is_mul t)) (seq.map PreTerm.inv_aux F)).
  apply: (ssrbool.introT seq.allP) => x /(ssrbool.elimT seq.mapP) [y yF ->].
  by apply: PreTerm.is_mul_inv_aux; exact: (ssrbool.elimT seq.allP wfF _ yF).
have cancMI : is_true (PreTerm.invs_canceled (seq.map PreTerm.inv_aux F)).
  exact: PreTerm.invs_canceled_map_inv wfF cancF.
rewrite (nonces_of_pre_term_factors (PreTerm.mul (seq.map PreTerm.inv_aux F))).
rewrite (PreTerm.factors_mul wfMI) (PreTerm.flatten_factors_Nmul_id NmMI).
rewrite (PreTerm.cancel_invs_canceled NmMI cancMI).
rewrite (_ : path.sort preorder.Order.le (seq.map PreTerm.inv_aux F) ≡ₚ seq.map PreTerm.inv_aux F); last first.
  by apply/(ssrbool.elimT perm_Perm); rewrite path.perm_sort.
congr union_list; rewrite /F; elim: (PreTerm.factors pt) => //= x fs IH.
by rewrite nonces_of_pre_term_inv_aux IH.
Qed.

Lemma nonces_of_term_TInv t : nonces_of_term (TInv t) = nonces_of_term t.
Proof.
rewrite !nonces_of_term_unseal /nonces_of_term_def unfold_TInv.
exact: nonces_of_pre_term_inv (wf_unfold_term t).
Qed.

Lemma nonces_of_pre_term_base_expo pt :
  nonces_of_pre_term pt =
  nonces_of_pre_term (PreTerm.base pt) ∪ nonces_of_pre_term (PreTerm.expo pt).
Proof. by case: pt => [o|o1 e1|[||] e1 e2|es] //=; rewrite union_empty_r_L. Qed.

Lemma nonces_of_term_base_exps t :
  nonces_of_term t = nonces_of_term (base t) ∪ ⋃ map nonces_of_term (exps t).
Proof.
transitivity (nonces_of_pre_term (PreTerm.base (unfold_term t)) ∪
              ⋃ map nonces_of_pre_term (PreTerm.exps (unfold_term t))).
  rewrite {1}nonces_of_term_unseal /nonces_of_term_def.
  rewrite (nonces_of_pre_term_base_expo (unfold_term t)).
  by rewrite (nonces_of_pre_term_factors (PreTerm.expo (unfold_term t))).
congr (_ ∪ _).
  by rewrite /base (nonces_of_term_fold (PreTerm.wf_base (wf_unfold_term t))).
rewrite /exps -[@seq.map]/@map map_map; congr union_list.
have /(ssrbool.elimT seq.allP) wfs := PreTerm.wf_exps (wf_unfold_term t).
apply: map_ext_in => pt /list_elem_of_In /(ssrbool.introT inP) pt_in.
by rewrite /= (nonces_of_term_fold (wfs _ pt_in)).
Qed.

Lemma nonces_of_term_TExpN t ts :
  is_true (negb (is_exp t)) -> is_true (atomic ts) ->
  nonces_of_term (TExpN t ts) = nonces_of_term t ∪ ⋃ map nonces_of_term (cancel_invs ts).
Proof.
move => tNexp atom.
have nexp : is_true (negb (PreTerm.is_exp (unfold_term t))).
  by move: tNexp; rewrite is_exp_unfold.
have bt : base t = t by rewrite /base (PreTerm.base_expN nexp) unfold_termK.
have et : exps t = [] by rewrite /exps (PreTerm.exps_expN nexp).
rewrite (nonces_of_term_base_exps (TExpN t ts)) base_TExpN bt.
congr (_ ∪ _).
rewrite (exps_TExpN t ts atom) et seq.cat0s.
rewrite (_ : path.sort _ (cancel_invs ts) ≡ₚ cancel_invs ts); last first.
  by apply/(ssrbool.elimT perm_Perm); rewrite path.perm_sort.
done.
Qed.

Lemma nonces_flatten_factors us :
  ⋃ map nonces_of_pre_term (seq.flatten (seq.map PreTerm.factors us)) =
  ⋃ map nonces_of_pre_term us.
Proof.
elim: us => [|u us IH] //=.
by rewrite map_app union_list_app_L -(nonces_of_pre_term_factors u) IH.
Qed.

(* [PreTerm.mul] cancels/sorts/flattens its argument, so its nonces are a subset
   of the union of the factors' nonces — no atomicity needed. *)
Lemma nonces_of_pre_term_mul_sub us :
  nonces_of_pre_term (PreTerm.mul us) ⊆ ⋃ map nonces_of_pre_term us.
Proof.
rewrite /PreTerm.mul.
set M := seq.flatten (seq.map PreTerm.factors us).
rewrite (_ : nonces_of_pre_term _ =
             ⋃ map nonces_of_pre_term
                 (path.sort preorder.Order.le (PreTerm.cancel_invs M))); last first.
  by case: (path.sort preorder.Order.le (PreTerm.cancel_invs M)) => [|t [|t' l]] //=;
     rewrite union_empty_r_L.
rewrite (_ : path.sort preorder.Order.le (PreTerm.cancel_invs M) ≡ₚ PreTerm.cancel_invs M);
  last by apply/(ssrbool.elimT perm_Perm); rewrite path.perm_sort.
have HM : ⋃ map nonces_of_pre_term M = ⋃ map nonces_of_pre_term us
  by rewrite /M nonces_flatten_factors.
rewrite -HM.
move => a /elem_of_union_list [X [/list_elem_of_fmap [x [-> xL]] aX]].
apply/elem_of_union_list; exists (nonces_of_pre_term x); split => //.
apply/list_elem_of_fmap; exists x; split => //.
by move: xL => /(ssrbool.introT inP) /(PreTerm.mem_cancel_invs) /(ssrbool.elimT inP).
Qed.

(* [PreTerm.exp] folds the new exponent into the base and cancels, so nonces are a
   subset of [nonces base ∪ nonces exponent] — no atomicity needed. *)
Lemma nonces_of_pre_term_exp_sub b e :
  nonces_of_pre_term (PreTerm.exp b e) ⊆ nonces_of_pre_term b ∪ nonces_of_pre_term e.
Proof.
rewrite /PreTerm.exp.
have Hbe := nonces_of_pre_term_base_expo b.
case: (eqtype.eq_op (PreTerm.mul [PreTerm.expo b; e]) (PreTerm.PTMul [])).
- set_solver.
- have Hmul := @nonces_of_pre_term_mul_sub [PreTerm.expo b; e].
  move: Hmul => /=; set_solver.
Qed.

(* The atomicity hypothesis is not needed: [TExpN t ts = TExp t (TMulN ts)], and the
   nonces of both [exp] and [mul] are subsets of their parts regardless of atomicity. *)
Lemma nonces_of_term_TExpN_subseteq t ts :
  nonces_of_term (TExpN t ts) ⊆ nonces_of_term t ∪ ⋃ map nonces_of_term ts.
Proof.
have Hts : ⋃ map nonces_of_term ts = ⋃ map nonces_of_pre_term (map unfold_term ts).
  congr union_list. elim: ts => [|t' ts IH] //=.
  by rewrite IH nonces_of_term_unseal /nonces_of_term_def.
rewrite Hts !nonces_of_term_unseal /nonces_of_term_def.
have -> : unfold_term (TExpN t ts) =
          PreTerm.exp (unfold_term t) (PreTerm.mul (map unfold_term ts)).
  by rewrite /TExpN unfold_TExp unfold_TMulN.
etrans; first exact: (@nonces_of_pre_term_exp_sub (unfold_term t)
                        (PreTerm.mul (map unfold_term ts))).
have Hmul := @nonces_of_pre_term_mul_sub (map unfold_term ts).
set_solver.
Qed.
Global Arguments nonces_of_term_TExpN_subseteq t ts : clear implicits.

Lemma nonces_of_term_TMulN ts :
  wf_mul_list ts ->
  nonces_of_term (TMulN ts) = ⋃ map nonces_of_term ts.
Proof.
move => wf; have wfU := wf_mul_list_unfold ts (proj2 (is_trueP _) wf).
have e : TMulN ts = fold_term (PreTerm.PTMul (map unfold_term ts)).
  apply: unfold_term_inj; rewrite unfold_TMulN (@fold_termK _ wfU).
  exact: (PreTerm.mul_factors wfU).
rewrite {1}e (nonces_of_term_fold wfU) /=.
rewrite -[@seq.map]/@map map_map; congr union_list.
apply: map_ext_in => x /list_elem_of_In /(ssrbool.introT inP) x_ts.
by rewrite /= nonces_of_term_unseal.
Qed.

Lemma nonces_of_term_tfactors t :
  nonces_of_term t = ⋃ map nonces_of_term (tfactors t).
Proof.
rewrite nonces_of_term_unseal /nonces_of_term_def
  (nonces_of_pre_term_factors (unfold_term t)) /tfactors.
congr union_list.
elim: (PreTerm.factors (unfold_term t)) (PreTerm.wf_factors (wf_unfold_term t))
  => //= pt pts IH wf.
have [wpt wpts] := ssrbool.elimT ssrbool.andP wf.
by rewrite IH // (@fold_termK pt wpt).
Qed.

Definition nonces_of_termE :=
  (nonces_of_term_TInv, nonces_of_term_TExpN, nonces_of_term_TMulN, nonces_of_termE').

Fixpoint ssubterms_pre_def t : gset term :=
  let subterms_pre_def t := {[fold_term t]} ∪ ssubterms_pre_def t in
  match t with
  | PreTerm.PT0 (O0Int _) => ∅
  | PreTerm.PT2 O2Pair t1 t2 => subterms_pre_def t1 ∪ subterms_pre_def t2
  | PreTerm.PT0 (O0Nonce _) => ∅
  | PreTerm.PT1 (O1Key _) t => subterms_pre_def t
  | PreTerm.PT2 O2Seal t1 t2 => subterms_pre_def t1 ∪ subterms_pre_def t2
  | PreTerm.PT1 O1Hash t => subterms_pre_def t
  | PreTerm.PT1 O1Inv t => subterms_pre_def t
  | PreTerm.PTExp b (PreTerm.PTMul us) =>
    subterms_pre_def b ∪ ⋃ map subterms_pre_def us
  | PreTerm.PTExp b e => subterms_pre_def b ∪ subterms_pre_def e
  | PreTerm.PTMul ts => ⋃ map subterms_pre_def ts
  end.

Definition subterms_def t := {[t]} ∪ ssubterms_pre_def (unfold_term t).
Arguments subterms_def /.
Definition subterms_aux : seal subterms_def. by eexists. Qed.
Definition subterms := unseal subterms_aux.
Lemma subterms_unseal : subterms = subterms_def.
Proof. exact: seal_eq. Qed.

Definition subterms_pre pt := {[fold_term pt]} ∪ ssubterms_pre_def pt.

Lemma subterms_preE pt :
  subterms_pre pt =
  {[fold_term pt]} ∪
  match pt with
  | PreTerm.PT0 _ => ∅
  | PreTerm.PT1 (O1Key _) t => subterms_pre t
  | PreTerm.PT1 O1Hash t => subterms_pre t
  | PreTerm.PT1 O1Inv t => subterms_pre t
  | PreTerm.PT2 O2Pair t1 t2 => subterms_pre t1 ∪ subterms_pre t2
  | PreTerm.PT2 O2Seal t1 t2 => subterms_pre t1 ∪ subterms_pre t2
  | PreTerm.PTExp b e => subterms_pre b ∪ ⋃ map subterms_pre (PreTerm.factors e)
  | PreTerm.PTMul ts => ⋃ map subterms_pre ts
  end.
Proof.
rewrite /subterms_pre; case: pt => [o|o e|[||] e1 e2|es] //=.
- by case: o.
- case: e2 => //= *; set_solver.
Qed.

Lemma subterms_fold pt :
  is_true (PreTerm.wf_term pt) -> subterms (fold_term pt) = subterms_pre pt.
Proof. move => wf; by rewrite subterms_unseal /subterms_def /subterms_pre (@fold_termK pt wf). Qed.

Lemma subterms_via_pre t : subterms t = subterms_pre (unfold_term t).
Proof. by rewrite subterms_unseal /subterms_def /subterms_pre unfold_termK. Qed.

Lemma subterms_pre_base_exps pt :
  subterms_pre pt =
  {[fold_term pt]} ∪ subterms_pre (PreTerm.base pt) ∪ ⋃ map subterms_pre (PreTerm.exps pt).
Proof.
case: (ssrbool.boolP (PreTerm.is_exp pt)) => [xp | Nxp].
- case: pt xp => [o|o e|[||] e1 e2|es] //= _; rewrite subterms_preE /=; set_solver.
- rewrite (PreTerm.base_expN Nxp) (PreTerm.exps_expN Nxp) /=.
  rewrite /subterms_pre; set_solver.
Qed.

Lemma subterms_base_exps t :
  subterms t = {[t]} ∪ subterms (base t) ∪ ⋃ map subterms (exps t).
Proof.
have hb : subterms_pre (PreTerm.base (unfold_term t)) = subterms (base t).
  by rewrite /base (subterms_fold (PreTerm.wf_base (wf_unfold_term t))).
have he : ⋃ map subterms_pre (PreTerm.exps (unfold_term t)) = ⋃ map subterms (exps t).
  rewrite /exps -[@seq.map]/@map map_map; congr union_list.
  have /(ssrbool.elimT seq.allP) wfs := PreTerm.wf_exps (wf_unfold_term t).
  apply: map_ext_in => pt /list_elem_of_In /(ssrbool.introT inP) pt_in.
  by rewrite /= (subterms_fold (wfs _ pt_in)).
by rewrite (subterms_via_pre t) (subterms_pre_base_exps (unfold_term t)) unfold_termK hb he.
Qed.

Lemma subtermsE' t :
  subterms t =
  {[t]} ∪
  match t with
  | TInt _ => ∅
  | TPair t1 t2 => subterms t1 ∪ subterms t2
  | TNonce _ => ∅
  | TKey _ t => subterms t
  | TSeal t1 t2 => subterms t1 ∪ subterms t2
  | THash t => subterms t
  | TNonFree pt _ _ => ssubterms_pre_def pt
  end.
Proof.
rewrite subterms_unseal /=.
case: t =>> //=; try by rewrite ?unfold_termK.
Qed.

Lemma subterms_TInv t :
  negb (is_mul t) -> negb (is_inv t) ->
  subterms (TInv t) = {[TInv t]} ∪ subterms t.
Proof.
move => /is_trueP Nm. rewrite is_inv_unfold. move /is_trueP => ?.
rewrite subterms_unseal /subterms_def.
by rewrite (unfold_TInv_Nmul Nm) PreTerm.inv_invN //= unfold_termK.
Qed.

Lemma subterms_TExpN t ts :
  is_true (negb (is_exp t)) -> is_true (atomic ts) ->
  subterms (TExpN t ts) = {[TExpN t ts]} ∪ subterms t ∪ ⋃ map subterms (cancel_invs ts).
Proof.
move => tNexp atom.
have nexp : is_true (negb (PreTerm.is_exp (unfold_term t))).
  by move: tNexp; rewrite is_exp_unfold.
have bt : base t = t by rewrite /base (PreTerm.base_expN nexp) unfold_termK.
have et : exps t = [] by rewrite /exps (PreTerm.exps_expN nexp).
rewrite (subterms_base_exps (TExpN t ts)) base_TExpN bt.
rewrite (exps_TExpN t ts atom) et seq.cat0s.
rewrite (_ : path.sort _ (cancel_invs ts) ≡ₚ cancel_invs ts); last first.
  by apply/(ssrbool.elimT perm_Perm); rewrite path.perm_sort.
done.
Qed.

Lemma subterms_TMulN ts :
  wf_mul_list ts ->
  subterms (TMulN ts) = {[TMulN ts]} ∪ ⋃ map subterms ts.
Proof.
move => wf; have wfU := wf_mul_list_unfold ts (proj2 (is_trueP _) wf).
have e : TMulN ts = fold_term (PreTerm.PTMul (map unfold_term ts)).
  apply: unfold_term_inj; rewrite unfold_TMulN (@fold_termK _ wfU).
  exact: (PreTerm.mul_factors wfU).
rewrite {1}e (subterms_fold wfU) subterms_preE -e /=.
congr (_ ∪ _).
rewrite -[@seq.map]/@map map_map; congr union_list.
apply: map_ext_in => x /list_elem_of_In /(ssrbool.introT inP) x_ts.
by rewrite /= subterms_via_pre.
Qed.

Lemma subterms_nonce t : is_nonce t → subterms t = {[t]}.
Proof.
by case: t => //= ? _; rewrite subtermsE' right_id_L.
Qed.

Definition subtermsE := (subterms_TInv, subterms_TExpN, subterms_TMulN, subtermsE').

Ltac solve_subtermsP :=
  intros;
  repeat match goal with
  | H : context[subterms (?X ?Y)] |- _ =>
      rewrite [subterms (X Y)]subtermsE /= in H
  | H : _ ∈ {[_]} |- _ =>
      rewrite elem_of_singleton in H;
      rewrite {}H
  | H : _ ∈ _ ∪ _ |- _ =>
      rewrite elem_of_union in H;
      destruct H
  | H : _ ∈ ∅ |- _ =>
      rewrite elem_of_empty in H;
      destruct H
  | H1 : ?P, H2 : ?P -> ?Q |- _ =>
      move/(_ H1) in H2
  end;
  eauto using subterm.

Lemma subtermsP t1 t2 : subterm t1 t2 ↔ t1 ∈ subterms t2.
Proof.
split.
- elim: t2 /; try by intros; rewrite subtermsE //; set_solver.
  + move => t' ts Nexp sub IH.
    have bt' : base t' = t'.
      rewrite /base; move: Nexp; rewrite is_exp_unfold => /is_trueP n.
      by rewrite (PreTerm.base_expN n) unfold_termK.
    rewrite (subterms_base_exps (TExpN t' ts)) base_TExpN bt'; set_solver.
  + move => t' t'' ts Nexp atom canc sub IH t''_ts.
    rewrite (subterms_TExpN (proj2 (is_trueP _) Nexp) (proj2 (is_trueP _) atom)).
    rewrite (cancel_invs_canceled ts (proj2 (is_trueP _) atom) (proj2 (is_trueP _) canc)) !elem_of_union; right.
    rewrite elem_of_union_list; exists (subterms t''); split => //.
    by rewrite list_elem_of_fmap; exists t''; split.
  + move => t'' ts wf sub IH t''_ts.
    rewrite (subterms_TMulN wf) elem_of_union; right.
    rewrite elem_of_union_list; exists (subterms t''); split => //.
    by rewrite list_elem_of_fmap; exists t''; split.
- elim: t2; try by solve_subtermsP.
  + move => t IHt Nexp ts IHts atom tsN0 sort canc.
    rewrite subtermsE //.
    rewrite (cancel_invs_canceled ts atom canc).
    rewrite !elem_of_union elem_of_union_list elem_of_singleton.
    case => [[-> | /IHt sub] | [X [/list_elem_of_fmap [t' [-> t'_ts]] t1_t']]].
    * exact: STRefl.
    * apply: STExp1; [exact: (proj1 (is_trueP _) Nexp)|exact: sub].
    * have sub' : subterm t1 t'.
        move: IHts t'_ts t1_t'; elim: (ts) => /= [_ /elem_of_nil //|t0 ts0 IH0 [IH1 IHrest]].
        rewrite elem_of_cons; case => [-> //|/(IH0 IHrest)] // h ?; exact: h.
      apply: (STExp2 (proj1 (is_trueP _) Nexp) (proj1 (is_trueP _) atom)
                     (proj1 (is_trueP _) canc) sub' t'_ts).
  + move => ts IHts atom sort canc szN1.
    have wf : is_true (wf_mul_list ts).
      rewrite /wf_mul_list; apply/(ssrbool.introT ssrbool.and4P); split;
        [exact: atom|exact: sort|exact: canc|exact: szN1].
    rewrite (subterms_TMulN (proj1 (is_trueP _) wf)).
    rewrite elem_of_union elem_of_union_list elem_of_singleton.
    case => [-> | [X [/list_elem_of_fmap [t' [-> t'_ts]] t1_t']]].
    * exact: STRefl.
    * have sub' : subterm t1 t'.
        move: IHts t'_ts t1_t'; elim: (ts) => /= [_ /elem_of_nil //|t0 ts0 IH0 [IH1 IHrest]].
        rewrite elem_of_cons; case => [-> //|/(IH0 IHrest)] // h ?; exact: h.
      apply: (STMul (proj1 (is_trueP _) wf) sub' t'_ts).
Qed.

Ltac solve_nonces_of_termP :=
  intros;
  repeat match goal with
  | H : context[nonces_of_term (?X ?Y)] |- _ =>
      rewrite [nonces_of_term (X Y)]nonces_of_termE /= in H
  | H : _ ∈ {[_]} |- _ =>
      rewrite elem_of_singleton in H;
      rewrite {}H
  | H : _ ∈ _ ∪ _ |- _ =>
      rewrite elem_of_union in H;
      destruct H
  | H : _ ∈ ∅ |- _ =>
      rewrite elem_of_empty in H;
      destruct H
  | H1 : ?P, H2 : ?P -> ?Q |- _ =>
      move/(_ H1) in H2
  end;
  eauto using subterm.

Lemma nonces_of_termP (a : nonce) t : subterm (TNonce a) t ↔ a ∈ nonces_of_term t.
Proof.
split.
- elim: t /; try by intros; rewrite nonces_of_termE; set_solver.
  + move => t' ts Nexp sub IH.
    have bt' : base t' = t'.
      rewrite /base; move: Nexp; rewrite is_exp_unfold => /is_trueP n.
      by rewrite (PreTerm.base_expN n) unfold_termK.
    rewrite (nonces_of_term_base_exps (TExpN t' ts)) base_TExpN bt'; set_solver.
  + move => t' t'' ts Nexp atom canc sub IH t''_ts.
    rewrite (nonces_of_term_TExpN (proj2 (is_trueP _) Nexp) (proj2 (is_trueP _) atom)).
    rewrite (cancel_invs_canceled ts (proj2 (is_trueP _) atom) (proj2 (is_trueP _) canc)) elem_of_union; right.
    rewrite elem_of_union_list; exists (nonces_of_term t''); split => //.
    by rewrite list_elem_of_fmap; exists t''; split.
  + move => t'' ts wf sub IH t''_ts.
    rewrite (nonces_of_term_TMulN wf) elem_of_union_list.
    exists (nonces_of_term t''); split => //.
    by rewrite list_elem_of_fmap; exists t''; split.
- elim: t; try by solve_nonces_of_termP.
  + move => t IHt Nexp ts IHts atom tsN0 sort canc.
    rewrite nonces_of_termE //.
    rewrite (cancel_invs_canceled ts atom canc) elem_of_union elem_of_union_list.
    case => [/IHt sub | [X [/list_elem_of_fmap [t' [-> t'_ts]] a_t']]].
    * apply: STExp1; [exact: (proj1 (is_trueP _) Nexp)|exact: sub].
    * have sub' : subterm (TNonce a) t'.
        move: IHts t'_ts a_t'; elim: (ts) => /= [_ /elem_of_nil //|t0 ts0 IH0 [IH1 IHrest]].
        rewrite elem_of_cons; case => [-> //|/(IH0 IHrest)] // h ?; exact: h.
      apply: (STExp2 (proj1 (is_trueP _) Nexp) (proj1 (is_trueP _) atom)
                     (proj1 (is_trueP _) canc) sub' t'_ts).
  + move => ts IHts atom sort canc szN1.
    have wf : is_true (wf_mul_list ts).
      rewrite /wf_mul_list; apply/(ssrbool.introT ssrbool.and4P); split;
        [exact: atom|exact: sort|exact: canc|exact: szN1].
    rewrite (nonces_of_term_TMulN (proj1 (is_trueP _) wf)) elem_of_union_list.
    case => [X [/list_elem_of_fmap [t' [-> t'_ts]] a_t']].
    have sub' : subterm (TNonce a) t'.
      move: IHts t'_ts a_t'; elim: (ts) => /= [_ /elem_of_nil //|t0 ts0 IH0 [IH1 IHrest]].
      rewrite elem_of_cons; case => [-> //|/(IH0 IHrest)] // h ?; exact: h.
    apply: (STMul (proj1 (is_trueP _) wf) sub' t'_ts).
Qed.

Lemma subterm_nonces_of_term t1 t2 :
  subterm t1 t2 → nonces_of_term t1 ⊆ nonces_of_term t2.
Proof.
elim: t2 / => //; try by intros; rewrite [nonces_of_term (_ _)]nonces_of_termE; set_solver.
- move => t' ts Nexp sub IH.
  have bt' : base t' = t'.
    rewrite /base; move: Nexp; rewrite is_exp_unfold => /is_trueP n.
    by rewrite (PreTerm.base_expN n) unfold_termK.
  rewrite (nonces_of_term_base_exps (TExpN t' ts)) base_TExpN bt'; set_solver.
- move => t' t'' ts Nexp atom canc sub IH t''_ts.
  rewrite (nonces_of_term_TExpN (proj2 (is_trueP _) Nexp) (proj2 (is_trueP _) atom)).
  rewrite (cancel_invs_canceled ts (proj2 (is_trueP _) atom) (proj2 (is_trueP _) canc)).
  have sub2 : nonces_of_term t'' ⊆ ⋃ map nonces_of_term ts.
    move => x x_t''; rewrite elem_of_union_list; exists (nonces_of_term t''); split => //.
    by rewrite list_elem_of_fmap; exists t''; split.
  set_solver.
- move => t'' ts wf sub IH t''_ts.
  rewrite (nonces_of_term_TMulN wf).
  have sub2 : nonces_of_term t'' ⊆ ⋃ map nonces_of_term ts.
    move => x x_t''; rewrite elem_of_union_list; exists (nonces_of_term t''); split => //.
    by rewrite list_elem_of_fmap; exists t''; split.
  set_solver.
Qed.

Definition Tag_def (N : namespace) :=
  TInt (Zpos (encode N)).
Definition Tag_aux : seal Tag_def. by eexists. Qed.
Definition Tag := unseal Tag_aux.
Lemma Tag_unseal : Tag = Tag_def. Proof. exact: seal_eq. Qed.

Global Instance Tag_inj : Inj (=) (=) Tag.
Proof. by rewrite Tag_unseal => ?? [] /(inj _ _ _). Qed.

Module Spec.

Implicit Types N : term.

Definition is_seal_key k :=
  match k with
  | TKey AEnc _ | TKey Sign _ | TKey SEnc _ => true
  | _ => false
  end.

Definition public_key_type kt :=
  match kt with
  | AEnc | Verify => true
  | _ => false
  end.

Definition skey t :=
  match t with
  | TKey AEnc t => TKey ADec t
  | TKey Verify t => TKey Sign t
  | _ => t
  end.

Definition pkey t :=
  match t with
  | TKey ADec t => TKey AEnc t
  | TKey Sign t => TKey Verify t
  | _ => t
  end.

Lemma aenc_pkey_inj (sk1 sk2 : aenc_key) :
  pkey sk1 = pkey sk2 → sk1 = sk2.
Proof. by rewrite keysE; case: sk1 sk2 => [?] [?] [->]. Qed.

Lemma sign_pkey_inj (sk1 sk2 : sign_key) :
  pkey sk1 = pkey sk2 → sk1 = sk2.
Proof. by rewrite keysE; case: sk1 sk2 => [?] [?] [->]. Qed.

Lemma senc_pkey_inj (sk1 sk2 : senc_key) :
  pkey sk1 = pkey sk2 → sk1 = sk2.
Proof. by rewrite keysE; case: sk1 sk2 => [?] [?] [->]. Qed.

Definition tag_def N (t : term) :=
  TPair N t.
Definition tag_aux : seal tag_def. by eexists. Qed.
Definition tag := unseal tag_aux.
Lemma tag_unseal : tag = tag_def. Proof. exact: seal_eq. Qed.

Lemma is_nonce_tag N t : is_nonce (tag N t) = false.
Proof. by rewrite tag_unseal. Qed.

Lemma is_exp_tag N t : is_exp (tag N t) = false.
Proof. by rewrite tag_unseal. Qed.

Definition untag_def N (t : term) :=
  match t with
  | TPair N' t =>
    if decide (N = N') then Some t else None
  | _ => None
  end.
Definition untag_aux : seal untag_def. by eexists. Qed.
Definition untag := unseal untag_aux.
Lemma untag_unseal : untag = untag_def. Proof. exact: seal_eq. Qed.

Lemma tagK N t : untag N (tag N t) = Some t.
Proof.
rewrite untag_unseal tag_unseal /untag_def /tag_def /=.
by rewrite decide_True_pi.
Qed.

#[global]
Instance tag_inj : Inj2 (=) (=) (=) tag.
Proof.
rewrite tag_unseal /tag_def => c1 t1 c2 t2 [] e ->.
split=> //; by apply: inj e.
Qed.

Lemma untagK N t1 t2 :
  untag N t1 = Some t2 ->
  t1 = tag N t2.
Proof.
rewrite untag_unseal tag_unseal /=.
case: t1=> [] // N' t1 /=.
by case: decide => // <- [<-].
Qed.

Lemma untag_tag_ne N1 N2 t :
  N1 ≠ N2 →
  Spec.untag N1 (Spec.tag N2 t) = None.
Proof.
move=> neq; rewrite Spec.untag_unseal Spec.tag_unseal /=.
rewrite decide_False //.
Qed.

Variant untag_spec N t : option term → Type :=
| UntagSome t' of t = Spec.tag N t' : untag_spec N t (Some t')
| UntagNone of (∀ t', t ≠ Spec.tag N t') : untag_spec N t None.

Lemma untagP N t : untag_spec N t (Spec.untag N t).
Proof.
case e: (Spec.untag N t) => [t'|]; constructor.
- by rewrite (Spec.untagK e).
- move=> t' e'; by rewrite e' Spec.tagK in e.
Qed.

Definition to_int t :=
  if t is TInt n then Some n else None.

Variant to_int_spec t : option Z → Type :=
| AsIntSome n of t = TInt n : to_int_spec t (Some n)
| AsIntNone of (∀ n, t ≠ TInt n) : to_int_spec t None.

Lemma to_intP t : to_int_spec t (Spec.to_int t).
Proof. by case: t => *; constructor; congruence. Qed.

Definition untuple t :=
  match t with
  | TPair t1 t2 => Some (t1, t2)
  | _ => None
  end.

Fixpoint proj t n {struct t} :=
  match t, n with
  | TPair t _, 0 => Some t
  | TPair _ t, S n => proj t n
  | _, _ => None
  end.

Definition to_key k : option (key_type * term) :=
  match k with
  | TKey kt t => Some (kt, t)
  | _ => None
  end.

Definition open_key k : option term :=
  match to_key k with
  | Some (kt, t) =>
      match kt with
      | AEnc => Some (TKey ADec t)
      | Sign => Some (TKey Verify t)
      | SEnc => Some (TKey SEnc t)
      | _ => None
      end
  | _ => None
  end.

Lemma open_key_aenc (sk : aenc_key) :
  open_key (Spec.pkey sk) = @Some term sk.
Proof. by rewrite keysE. Qed.

Lemma open_key_sign (sk : sign_key) :
  open_key sk = Some (Spec.pkey sk).
Proof. by rewrite keysE. Qed.

Lemma open_key_senc (sk : senc_key) :
  open_key sk = @Some term sk.
Proof. by rewrite keysE. Qed.

Lemma open_key_aencK pk (sk : aenc_key) :
  open_key pk = @Some term sk → pk = pkey sk.
Proof.
rewrite keysE; case: sk => seed /=.
by case: pk => //= - [] // ?; case=> ->.
Qed.

Lemma open_key_signK k (sk : sign_key) :
  open_key k = Some (Spec.pkey sk) → k = sk.
Proof.
rewrite keysE; case: sk => seed /=.
by case: k => //= - [] // ?; case=> ->.
Qed.

Lemma open_key_sencK k' (k : senc_key) :
  open_key k' = @Some term k → k' = k.
Proof.
rewrite keysE; case: k => seed /=.
by case: k' => //= - [] // ?; case=> ->.
Qed.

Lemma open_key_tsize t1 t2 : open_key t1 = Some t2 → tsize t2 = tsize t1.
Proof.
by case: t1 => // - [] //= t [<-]; rewrite tsizeE.
Qed.

Definition open k t : option term :=
  match t with
  | TSeal k_t t =>
    if decide (open_key k_t = Some k) then Some t else None
  | _ => None
  end.

Variant open_spec k t : option term → Type :=
| OpenSome k_t t'
  of open_key k_t = Some k & t = TSeal k_t t'
  : open_spec k t (Some t')
| OpenNone : open_spec k t None.

Lemma openP k t : open_spec k t (open k t).
Proof.
case: t; eauto using open_spec => k_t t /=.
by case: decide => [e|_]; eauto using open_spec.
Qed.

Definition is_key t :=
  match t with
  | TKey kt _ => Some kt
  | _ => None
  end.

Variant is_key_spec t : option key_type → Type :=
| IsKeySome kt k of t = TKey kt k : is_key_spec t (Some kt)
| IsKeyNone of (∀ kt k, t ≠ TKey kt k) : is_key_spec t None.

Lemma is_keyP t : is_key_spec t (is_key t).
Proof.
case: t; try by right.
by move=> kt t; eleft.
Qed.

Definition has_key_type kt t :=
  match is_key t with
  | Some kt' => bool_decide (kt = kt')
  | None => false
  end.

Definition of_list_aux : seal (foldr TPair (TInt 0)). by eexists. Qed.
Definition of_list := unseal of_list_aux.
Lemma of_list_unseal : of_list = foldr TPair (TInt 0).
Proof. exact: seal_eq. Qed.

Lemma of_list_tsize t ts : t ∈ ts → tsize t < tsize (of_list ts).
Proof.
rewrite of_list_unseal; elim: ts => [/elem_of_nil |t' ts IH /elem_of_cons] //=.
rewrite [tsize (TPair _ _)]tsizeE ssrnat.addnE; case=> [<-|/IH t_ts]; lia.
Qed.

Lemma is_nonce_of_list ts : is_nonce (of_list ts) = false.
Proof. by rewrite of_list_unseal; case: ts. Qed.

Lemma is_exp_of_list ts : is_exp (of_list ts) = false.
Proof. by rewrite of_list_unseal; case: ts. Qed.

Fixpoint to_list t : option (list term) :=
  match t with
  | TInt 0 => Some []
  | TPair t1 t2 =>
    match to_list t2 with
    | Some l => Some (t1 :: l)
    | None => None
    end
  | _ => None
  end.

Lemma of_listK l : to_list (of_list l) = Some l.
Proof. rewrite of_list_unseal; by elim: l => //= t l ->. Qed.

Lemma to_listK t ts :
  to_list t = Some ts →
  t = of_list ts.
Proof.
rewrite of_list_unseal /=; elim/term_ind': t ts => //.
  by case=> [] // _ [<-].
move=> t _ ts' IH /= ts.
case e: to_list => [ts''|] // [<-].
by rewrite /= (IH _ e).
Qed.

Inductive to_list_spec : term → option (list term) → Type :=
| ToListSome ts : to_list_spec (of_list ts) (Some ts)
| ToListNone t  : to_list_spec t None.

Lemma to_listP t : to_list_spec t (to_list t).
Proof.
case e: to_list => [ts|]; last constructor.
by rewrite (to_listK e); constructor.
Qed.

Lemma of_list_inj : Inj eq eq of_list.
Proof.
move=> ts1 ts2 e; apply: Some_inj.
by rewrite -of_listK e of_listK.
Qed.

Definition enc k c t := TSeal k (tag c t).

Definition dec k c t :=
  match open k t with
  | Some t => untag c t
  | None => None
  end.

Variant dec_spec k c t : option term → Type :=
| DecSome k_t t'
  of open_key k_t = Some k
  &  t = TSeal k_t (tag c t')
  : dec_spec k c t (Some t')
| DecNone : dec_spec k c t None.

Lemma decP k c t : dec_spec k c t (dec k c t).
Proof.
rewrite /dec.
case: openP; eauto using dec_spec.
move=> {}k_t {}t e ->.
case: untagP; eauto using dec_spec.
move=> {}t ->; eauto using dec_spec.
Qed.

Lemma decK k1 k2 c t t' :
  open_key k1 = Some k2 →
  dec k2 c t = Some t' →
  t = TSeal k1 (tag c t').
Proof.
rewrite /Spec.dec /=.
case: t => [] //= k_t t.
case: decide => // k_t_k2 k1_k2 /untagK <-.
rewrite /open_key in k_t_k2 k1_k2.
case: k_t k1 => [] // kt1 ? [] //= kt2 ? in k_t_k2 k1_k2 *.
case: kt1 kt2 => [] //= [] //= in k_t_k2 k1_k2 *; congruence.
Qed.

Definition zero : term := TInt 0.

End Spec.

Arguments repr_term /.
Arguments Spec.tag_def /.
Arguments Spec.untag_def /.

#[global]
Existing Instance Spec.of_list_inj.

Lemma subterm_tag c t1 t2 : subterm t1 t2 → subterm t1 (Spec.tag c t2).
Proof. by rewrite Spec.tag_unseal; eauto using subterm. Qed.

#[global]
Hint Resolve STRefl : core.

Lemma invs_canceledP ts :
  (forall t, t ∈ ts -> TInv t ∉ ts) ↔ invs_canceled ts.
Proof.
split.
- move => H. apply /is_trueP /(ssrbool.introT invs_canceledP).
  by move => ? /(ssrbool.elimT inP) /H /(ssrbool.introN inP).
- move => /is_trueP /(ssrbool.elimT invs_canceledP) H.
  by move => ? /(ssrbool.introT inP) /H /(ssrbool.elimN inP).
Qed.

Global Instance invs_canceled_proper : Proper ((≡ₚ) ==> (=)) invs_canceled.
Proof. by move => ts1 ts2 /(ssrbool.introT perm_Perm) /perm_invs_canceled. Qed.

Lemma invs_canceled1 t : is_true (negb (is_mul t)) -> invs_canceled [t].
Proof. move => Nm. exact /is_trueP /(invs_canceled_Nmul1 Nm). Qed.

Lemma invs_canceled_cons t ts :
  is_true (negb (is_mul t)) ->
  invs_canceled (t :: ts) ↔ (TInv t ∉ ts) ∧ invs_canceled ts.
Proof.
move => Nm.
rewrite (invs_canceled_cons Nm); split.
- by move => /andb_prop_elim [/is_trueP /(ssrbool.elimN inP)].
- move => [/(ssrbool.introN inP) /is_trueP ? ?]. exact /andb_prop_intro.
Qed.

Lemma invs_canceled2 t1 t2 :
  is_true (negb (is_mul t1)) -> is_true (negb (is_mul t2)) ->
  invs_canceled [t1 ; t2] ↔ (t1 ≠ TInv t2).
Proof.
move => Nm1 Nm2.
rewrite (invs_canceled2_Nmul Nm1 Nm2); split.
- by move => /is_trueP /(ssrbool.elimN eqtype.eqP).
- by move => /(ssrbool.introN eqtype.eqP) /is_trueP.
Qed.

Lemma invs_canceled_exps t : invs_canceled (exps t).
Proof. exact /is_trueP /invs_canceled_exps. Qed.

Lemma invs_canceled_cons_exps t1 t2 :
  is_true (negb (is_mul t1)) ->
  invs_canceled (t1 :: exps t2) ↔ (TInv t1 ∉ exps t2).
Proof.
move => Nm.
rewrite (invs_canceled_cons_exps t2 Nm); split.
- by move => /is_trueP /(ssrbool.elimN inP).
- by move => /(ssrbool.introN inP) /is_trueP.
Qed.

Lemma cancel_invs_canceled ts :
  is_true (atomic ts) -> invs_canceled ts -> cancel_invs ts = ts.
Proof. move => atom /is_trueP ic. exact: (cancel_invs_canceled ts atom ic). Qed.

Lemma exps_TExpN t ts :
  is_true (atomic ts) -> exps (TExpN t ts) ≡ₚ cancel_invs (exps t ++ ts).
Proof.
move => atom.
apply/(ssrbool.elimT perm_Perm).
by rewrite (exps_TExpN _ _ atom) path.perm_sort.
Qed.

(*
Lemma is_exp_TExpN t ts :
  is_exp (TExpN t ts) = implb (bool_decide (ts = [])) (is_exp t).
Proof.
rewrite is_exp_TExpN -eq_op_bool_decide implb_orb.
by case: ts.
Qed.
*)

Lemma base_exps_inj t1 t2 :
  base t1 = base t2 →
  exps t1 ≡ₚ exps t2 →
  t1 = t2.
Proof.
move=> eb /(ssrbool.introT perm_Perm) ?.
by apply: base_exps_inj.
Qed.

Lemma TExp_TExpN t1 ts1 t2 : TExp (TExpN t1 ts1) t2 = TExpN t1 (t2 :: ts1).
Proof.
have -> : TExp (TExpN t1 ts1) t2 = TExpN (TExpN t1 ts1) [t2].
  by rewrite /TExpN TMulN1.
by rewrite TExpNA -[@seq.cat]/@app [_ ++ _]comm.
Qed.

Lemma count_exp_TExpNW t1 t2 ts :
  is_true (atomic ts) ->
  (∀ t, t ∈ ts → t1 ≠ TInv t) →
  (count_exp t1 t2 ≤ count_exp t1 (TExpN t2 ts))%Z.
Proof.
elim: ts => [|t ts IH]; first by move => _ _; rewrite TExpN0; lia.
move => atom t1_ts.
move: (atom); rewrite /atomic /= => /(ssrbool.elimT ssrbool.andP) [Nmt atom'].
rewrite -TExp_TExpN; set t2' := TExpN t2 ts.
have ?: (count_exp t1 t2' ≤ count_exp t1 (TExp t2' t))%Z.
  apply: (count_exp_TExpW (proj1 (is_trueP _) Nmt)); move/(_ t): t1_ts; apply.
  rewrite elem_of_cons; by eauto.
suff: (count_exp t1 t2 ≤ count_exp t1 t2')%Z by lia.
apply: (IH atom') => t' t'_ts; apply: t1_ts; rewrite elem_of_cons; eauto.
Qed.

Lemma elem_of_TExpN2l g t1 t2 :
  is_true (negb (is_mul t1)) -> is_true (negb (is_mul t2)) ->
  t1 ≠ TInv t2 →
  TInv t1 ∉ exps g →
  t1 ∈ exps (TExpN g [t1; t2]).
Proof.
move=> Nm1 Nm2 t1_t2 t1_g.
rewrite (not_elem_of_TInv_exps g (proj1 (is_trueP _) Nm1)) -count_exp_gt0 in t1_g.
have e : TExpN g [t1; t2] = TExp (TExp g t1) t2.
  rewrite (_ : TExp g t1 = TExpN g [t1]); last by rewrite /TExpN TMulN1.
  rewrite TExp_TExpN; exact: TExpC2.
rewrite e -count_exp_gt0 (count_exp_TExp t1 (TExp g t1) (proj1 (is_trueP _) Nm2)).
rewrite (@decide_False _ (t1 = TInv t2)); last exact: t1_t2.
by case: decide; lia.
Qed.

Lemma elem_of_TExpN2r g t1 t2 :
  is_true (negb (is_mul t1)) -> is_true (negb (is_mul t2)) ->
  t1 ≠ TInv t2 →
  TInv t2 ∉ exps g →
  t2 ∈ exps (TExpN g [t1; t2]).
Proof.
move=> Nm1 Nm2 t1_t2 t2_g.
rewrite TExpC2.
apply: (elem_of_TExpN2l Nm2 Nm1); last exact: t2_g.
by move=> contra; apply: t1_t2; rewrite contra TInvK.
Qed.

Lemma base_expN t : ¬ is_exp t → base t = t.
Proof.
move=> tNX; apply: base_expN.
apply/(ssrbool.introN ssrbool.idP).
by rewrite is_trueP.
Qed.

Lemma exps_expN t : ¬ is_exp t → exps t = [].
Proof.
move=> tNX; apply: exps_expN.
apply/(ssrbool.introN ssrbool.idP).
by rewrite is_trueP.
Qed.

Lemma exps_TExpN' t ts :
  ¬ is_exp t -> is_true (atomic ts) ->
  invs_canceled ts ->
  exps (TExpN t ts) ≡ₚ ts.
Proof.
move => ? atom canc.
by rewrite (@exps_TExpN t ts atom) exps_expN //
   (cancel_invs_canceled atom canc).
Qed.

Lemma is_exp_base t : ¬ is_exp (base t).
Proof.
rewrite (ssrbool.negbTE (is_exp_base t)) /=. by auto.
Qed.
Hint Resolve is_exp_base : core.

Lemma parity_cancel_invs ts : Nat.odd (length (cancel_invs ts)) = Nat.odd (length ts).
Proof. by rewrite !oddE !sizeE parity_cancel_invs. Qed.
