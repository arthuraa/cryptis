From cryptis Require Import lib.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From deriving Require Import deriving.
From Stdlib Require Import ZArith.ZArith Lia.
From iris.heap_lang Require locations.
From cryptis.core Require Export pre_term.

Import Order.POrderTheory Order.TotalTheory.

Unset Elimination Schemes.
Inductive term :=
| TInt of Z
| TPair of term & term
| TNonce of locations.loc
| TKey of key_type & term
| TSeal of term & term
| THash of term
| TInv' pt of PreTerm.wf_term (PreTerm.PT1 O1Inv pt)
| TExpN' pt pts of PreTerm.wf_term (PreTerm.PTExp pt pts).

Record aenc_key := AEncKey {
  seed_of_aenc_key : term;
}.

Record sign_key := SignKey {
  seed_of_sign_key : term;
}.

Record senc_key := SEncKey {
  seed_of_senc_key : term;
}.
Set Elimination Schemes.

Definition term_of_aenc_key_def sk := TKey ADec (seed_of_aenc_key sk).
Fact term_of_aenc_key_key : unit. exact: tt. Qed.
Definition term_of_aenc_key :=
  locked_with term_of_aenc_key_key term_of_aenc_key_def.
Lemma term_of_aenc_keyE : term_of_aenc_key = term_of_aenc_key_def.
Proof. exact: locked_withE. Qed.
Coercion term_of_aenc_key : aenc_key >-> term.

Definition term_of_sign_key_def sk := TKey Sign (seed_of_sign_key sk).
Fact term_of_sign_key_key : unit. exact: tt. Qed.
Definition term_of_sign_key :=
  locked_with term_of_sign_key_key term_of_sign_key_def.
Lemma term_of_sign_keyE : term_of_sign_key = term_of_sign_key_def.
Proof. exact: locked_withE. Qed.
Coercion term_of_sign_key : sign_key >-> term.

Definition term_of_senc_key_def sk := TKey SEnc (seed_of_senc_key sk).
Fact term_of_senc_key_key : unit. exact: tt. Qed.
Definition term_of_senc_key :=
  locked_with term_of_senc_key_key term_of_senc_key_def.
Lemma term_of_senc_keyE : term_of_senc_key = term_of_senc_key_def.
Proof. exact: locked_withE. Qed.
Coercion term_of_senc_key : senc_key >-> term.

Definition keysE :=
  (term_of_aenc_keyE, term_of_sign_keyE, term_of_senc_keyE).

Lemma term_of_aenc_key_inj : injective term_of_aenc_key.
Proof. rewrite keysE. by case=> [?] [?] [->]. Qed.

Lemma term_of_sign_key_inj : injective term_of_sign_key.
Proof. rewrite keysE. by case=> [?] [?] [->]. Qed.

Lemma term_of_senc_key_inj : injective term_of_senc_key.
Proof. rewrite keysE. by case=> [?] [?] [->]. Qed.

(* We use a different name for the default induction scheme, as it does not
   allow us to recurse under exponentials.  Later, we'll prove term_ind, which
   does allow this. *)
Scheme term_ind' := Induction for term Sort Prop.

Fixpoint unfold_term t :=
  match t with
  | TInt n => PreTerm.PT0 (O0Int n)
  | TPair t1 t2 => PreTerm.PT2 O2Pair (unfold_term t1) (unfold_term t2)
  | TNonce l => PreTerm.PT0 (O0Nonce l)
  | TKey kt t => PreTerm.PT1 (O1Key kt) (unfold_term t)
  | TSeal k t => PreTerm.PT2 O2Seal (unfold_term k) (unfold_term t)
  | THash t => PreTerm.PT1 O1Hash (unfold_term t)
  | TInv' pt _ => PreTerm.PT1 O1Inv pt
  | TExpN' pt pts _ => PreTerm.PTExp pt pts
  end.

Fixpoint fold_term_predef pt :=
  match pt with
  | PreTerm.PT0 (O0Int n) => TInt n
  | PreTerm.PT2 O2Pair pt1 pt2 => TPair (fold_term_predef pt1) (fold_term_predef pt2)
  | PreTerm.PT0 (O0Nonce l) => TNonce l
  | PreTerm.PT1 (O1Key kt) pt => TKey kt (fold_term_predef pt)
  | PreTerm.PT2 O2Seal k pt => TSeal (fold_term_predef k) (fold_term_predef pt)
  | PreTerm.PT1 O1Hash pt => THash (fold_term_predef pt)
  | PreTerm.PT1 O1Inv pt' =>
    if boolP (PreTerm.wf_term (PreTerm.PT1 O1Inv pt')) is AltTrue pf then
      TInv' pt' pf
    else TInt 0 (*should never*)
  | PreTerm.PTExp pt' pts' =>
    if boolP (PreTerm.wf_term (PreTerm.PTExp pt' pts')) is AltTrue pf then
      TExpN' pt' pts' pf
    else TInt 0 (*should never*)
  end.

Definition fold_term_def pt := fold_term_predef (PreTerm.normalize pt).

Lemma wf_unfold_term t : PreTerm.wf_term (unfold_term t).
Proof. by elim/term_ind': t=> //= ? -> ? ->. Qed.

Lemma wf_unfold_terms ts : all PreTerm.wf_term [seq unfold_term i | i <- ts].
Proof. elim: ts => //= ? ? ->. by rewrite wf_unfold_term.  Qed.

Fact fold_term_key : unit. Proof. exact: tt. Qed.
Definition fold_term :=
  locked_with fold_term_key fold_term_def.
Canonical fold_term_unlockable := [unlockable of fold_term].

Lemma unfold_termK : cancel unfold_term fold_term.
Proof.
rewrite [fold_term]unlock => t.
rewrite /fold_term_def PreTerm.normalize_wf ?wf_unfold_term //.
elim /term_ind': t => //=.
- by move => t1 -> t2 ->.
- by move => kt t ->.
- by move => t1 -> t2 ->.
- by move => t ->.
- move => pt wf. move: (TInv' pt) (wf) => /=. rewrite wf. move: (boolP true).
  move: {3} (true) => b pf. case: pf => // ? t ?. congr t. apply: bool_irrelevance.
- move => pt pts wf. move: (TExpN' pt pts) (wf) => /=. rewrite wf. move: (boolP true).
  move: {3} (true) => b pf. case: pf => // ? t ?. congr t. apply: bool_irrelevance.
Qed.

Lemma unfold_fold pt : unfold_term (fold_term pt) = PreTerm.normalize pt.
Proof.
rewrite [fold_term]unlock. rewrite /fold_term_def.
have := PreTerm.wf_normalize pt. elim: (PreTerm.normalize pt) => //=.
- move => [] //.
- move => [?||] t IH wf_t /=.
  + by rewrite IH.
  + by rewrite IH.
  + move: (boolP _). move: {3} (_ && _) => b. case => //. by rewrite wf_t.
- move => [] t1 IH1 t2 IH2 /andP [wf1 wf2] /=; rewrite IH1 //; rewrite IH2 //.
- move => t IH ts IHs wf. move: (boolP _). move: {3} (_ && _) => b. case => //. by rewrite wf.
Qed.

Lemma fold_termK pt : PreTerm.wf_term pt -> unfold_term (fold_term pt) = pt.
Proof.
by move=> wf; rewrite unfold_fold PreTerm.normalize_wf.
Qed.

Lemma fold_normalize pt : fold_term (PreTerm.normalize pt) = fold_term pt.
Proof. by rewrite -unfold_fold unfold_termK. Qed.

Lemma unfold_term_inj : injective unfold_term.
Proof. exact: can_inj unfold_termK. Qed.

Implicit Types (t k : term) (ts : seq term).

Section TInv.

Fact TInv_key : unit. Proof. exact: tt. Qed.
Definition TInv :=
  locked_with TInv_key (
      fun t => fold_term (PreTerm.inv (unfold_term t))
  ).
Canonical TInv_unlock := [unlockable of TInv].

End TInv.

Section TExp.

Fact TExpN_key : unit. Proof. exact: tt. Qed.
Definition TExpN :=
  locked_with TExpN_key (
    fun t ts =>
      fold_term (PreTerm.exp (unfold_term t) (map unfold_term ts))
  ).
Canonical TExpN_unlock := [unlockable of TExpN].

End TExp.

Notation TExp t1 t2 := (TExpN t1 [:: t2]).

HB.instance Definition _ :=
  Equality.copy term (can_type unfold_termK).
HB.instance Definition _ :=
  Choice.copy term (can_type unfold_termK).
HB.instance Definition _ :=
  Countable.copy term (can_type unfold_termK).
HB.instance Definition _ : Order.Total _ term :=
  Order.CanIsTotal Order.default_display unfold_termK.

HB.instance Definition _ := [isNew for seed_of_aenc_key].
HB.instance Definition _ := [Equality of aenc_key by <:].
HB.instance Definition _ := [Choice of aenc_key by <:].
HB.instance Definition _ := [Countable of aenc_key by <:].
HB.instance Definition _ := [Order of aenc_key by <:].

HB.instance Definition _ := [isNew for seed_of_sign_key].
HB.instance Definition _ := [Equality of sign_key by <:].
HB.instance Definition _ := [Choice of sign_key by <:].
HB.instance Definition _ := [Countable of sign_key by <:].
HB.instance Definition _ := [Order of sign_key by <:].

HB.instance Definition _ := [isNew for seed_of_senc_key].
HB.instance Definition _ := [Equality of senc_key by <:].
HB.instance Definition _ := [Choice of senc_key by <:].
HB.instance Definition _ := [Countable of senc_key by <:].
HB.instance Definition _ := [Order of senc_key by <:].

Lemma normalize_unfold1 t :
  PreTerm.normalize (unfold_term t) = unfold_term t.
Proof. by rewrite PreTerm.normalize_wf // wf_unfold_term. Qed.

Lemma normalize_unfoldn ts :
  map PreTerm.normalize (map unfold_term ts) = map unfold_term ts.
Proof.
rewrite map_id_in // => ? /mapP [] {}t t_ts ->.
exact: normalize_unfold1.
Qed.

Lemma unfold_TInv t : unfold_term (TInv t) = PreTerm.inv (unfold_term t).
Proof.
by rewrite unlock unfold_fold PreTerm.normalize_wf ?PreTerm.wf_inv ?wf_unfold_term.
Qed.

Lemma unfold_TExpN t ts :
  unfold_term (TExpN t ts)
  = PreTerm.exp (unfold_term t) (map unfold_term ts).
Proof.
    rewrite unlock unfold_fold PreTerm.normalize_wf => //.
    rewrite PreTerm.wf_exp => //.
    apply wf_unfold_term.
    apply wf_unfold_terms.
Qed.

Lemma fold_termE pt :
  fold_term pt =
  match pt with
  | PreTerm.PT0 (O0Int n) => TInt n
  | PreTerm.PT2 O2Pair pt1 pt2 => TPair (fold_term pt1) (fold_term pt2)
  | PreTerm.PT0 (O0Nonce l) => TNonce l
  | PreTerm.PT1 (O1Key kt) pt => TKey kt (fold_term pt)
  | PreTerm.PT2 O2Seal k pt => TSeal (fold_term k) (fold_term pt)
  | PreTerm.PT1 O1Hash pt => THash (fold_term pt)
  | PreTerm.PT1 O1Inv pt => TInv (fold_term pt)
  | PreTerm.PTExp pt pts => TExpN (fold_term pt) (map fold_term pts)
  end.
Proof.
apply /unfold_term_inj. rewrite unfold_fold.
case: pt => //=.
- by case.
- case => [?? | ? | p] //=.
  + by rewrite unfold_fold.
  + by rewrite unfold_fold.
  + by rewrite unfold_TInv unfold_fold.
- case => [?? | ??] /=; by rewrite !unfold_fold.
- move => pt pts. rewrite unfold_TExpN unfold_fold -map_comp.
  by under eq_map => ? do rewrite -unfold_fold.
Qed.

Definition base t :=
  if t is TExpN' pt _ _ then fold_term pt else t.
Definition exps t :=
  if t is TExpN' _ pts _ then map fold_term pts else [::].

Lemma unfold_base t : unfold_term (base t) = PreTerm.base (unfold_term t).
Proof.
case: t => //= ?? wf; rewrite fold_termK //.
by case/and5P: wf.
Qed.

Lemma unfold_exps t :
  map unfold_term (exps t) = PreTerm.exps (unfold_term t).
Proof.
case: t => //= ?? /and5P [_ _ /allP wfs _ _].
rewrite -map_comp map_id_in //= => ? /wfs ?.
by rewrite /= fold_termK.
Qed.

Lemma TInv_Nid t : TInv t != t.
Proof. by rewrite -(eqtype.inj_eq unfold_term_inj) unfold_TInv PreTerm.inv_Nid. Qed.

Lemma TInvK : involutive TInv.
Proof.
move => ?.
by rewrite unlock unfold_fold PreTerm.normalize_wf ?PreTerm.wf_inv ?wf_unfold_term //
  PreTerm.inv_involutive ?wf_unfold_term // unfold_termK.
Qed.

Lemma TExpN_perm t ts1 ts2 : perm_eq ts1 ts2 -> TExpN t ts1 = TExpN t ts2.
Proof.
move => ?; apply: unfold_term_inj; rewrite !unfold_TExpN. apply: PreTerm.perm_exp.
 - exact: wf_unfold_term.
 - exact: wf_unfold_terms.
 - exact: perm_map.
Qed.

Lemma TExpNC t ts1 ts2 : TExpN t (ts1 ++ ts2) = TExpN t (ts2 ++ ts1).
Proof. by apply: TExpN_perm; rewrite perm_catC. Qed.

Lemma base_TExpN t ts : base (TExpN t ts) = base t.
Proof.
apply: unfold_term_inj; rewrite !unfold_base unfold_TExpN.
rewrite PreTerm.base_exp //. exact: wf_unfold_term.
Qed.

Definition cancel_exps ts :=
  map fold_term (PreTerm.cancel_exps (map unfold_term ts)).

Lemma perm_cancel_exps ts1 ts2 :
  perm_eq ts1 ts2 -> perm_eq (cancel_exps ts1) (cancel_exps ts2).
Proof.
move => ?. rewrite /cancel_exps.
apply perm_map. apply PreTerm.perm_cancel_exps.
- apply wf_unfold_terms.
- exact: perm_map.
Qed.

Lemma count_map_fold t pts :
  all PreTerm.wf_term pts ->
  count_mem t (map fold_term pts) = count_mem (unfold_term t) pts.
Proof.
elim: pts => //= [pt' ? IH] /andP [wf' ?]. rewrite IH //.
case: (pt' =P unfold_term t) => [/(canLR unfold_termK) /eqP -> | /eqP neq] //.
rewrite -(PreTerm.normalize_wf wf') -unfold_fold (eqtype.inj_eq unfold_term_inj) in neq.
by move: neq => /negbTE ->.
Qed.

Lemma count_cancel t ts :
  count_mem t (cancel_exps ts) = count_mem t ts - count_mem (TInv t) ts.
Proof.
by rewrite /cancel_exps count_map_fold ?PreTerm.wf_cancel_exps ?wf_unfold_terms //
  PreTerm.count_cancel ?wf_unfold_term ?wf_unfold_terms // -unfold_TInv !count_map.
Qed.

Lemma count_perm_cancel ts1 ts2 :
  (forall t, count_mem t ts1 - count_mem (TInv t) ts1 =
        count_mem t ts2 - count_mem (TInv t) ts2) <->
  perm_eq (cancel_exps ts1) (cancel_exps ts2).
Proof.
split.
- move => wt_eq. apply /allP => /= ? _. by rewrite !count_cancel wt_eq.
- move => *. rewrite -!count_cancel. exact: permP.
Qed.

Lemma count_perm_cancel_redux ts1 ts2 :
  (forall t, count_mem t ts1 + count_mem (TInv t) ts2 =
        count_mem t ts2 + count_mem (TInv t) ts1) <->
  perm_eq (cancel_exps ts1) (cancel_exps ts2).
Proof.
rewrite -count_perm_cancel !addnE !subnE.
split => H t; have := H t; first lia.
have := H (TInv t). rewrite TInvK. lia.
Qed.

Lemma count_TInv_cancel t ts :
  count_mem t (cancel_exps ts) != 0 -> count_mem (TInv t) (cancel_exps ts) == 0.
Proof. by rewrite !count_cancel TInvK -ltnNge => /ltnW. Qed.

Lemma cancel_exps_cat ts1 ts2 :
  perm_eq (cancel_exps (cancel_exps ts1 ++ ts2))
          (cancel_exps (ts1 ++ ts2)).
Proof.
apply count_perm_cancel => t. rewrite !count_cat.
case: (count_mem t (cancel_exps ts1) =P 0)
    => /eqP => [| /count_TInv_cancel];
      rewrite !count_cancel TInvK => /[dup] ? /eqP ->;
      rewrite add0n !subnDA.
- by rewrite addnC subnBA.
- by rewrite addnBAC.
Qed.

Lemma perm_cancel_exps_catl ts1 ts2 ts :
  perm_eq (cancel_exps (ts ++ ts1)) (cancel_exps (ts ++ ts2)) =
  perm_eq (cancel_exps ts1) (cancel_exps ts2).
Proof.
apply /(sameP idP); apply /(iffP idP);
move => /count_perm_cancel_redux wt_eq; apply count_perm_cancel_redux => t;
have := wt_eq t; rewrite !count_cat !addnE; lia.
Qed.

Lemma count_map_TInv t ts:
  count_mem t (map TInv ts) = count_mem (TInv t) ts.
Proof. elim: ts => //= [?? ->]. by rewrite (inv_eq TInvK). Qed.

Lemma cancel_exps_cat_invs ts1 ts2 :
  perm_eq (cancel_exps (ts1 ++ ts2 ++ map TInv ts2)) (cancel_exps ts1).
Proof.
apply count_perm_cancel.
move => t. rewrite !count_cat !count_map_TInv /= TInvK !addnE !subnE. lia.
Qed.

Lemma exps_TExpN t ts :
  exps (TExpN t ts) = sort <=%O (cancel_exps (exps t ++ ts)).
Proof.
apply: (inj_map unfold_term_inj). rewrite unfold_exps -sort_map -map_comp.
under eq_map => ? do rewrite /= unfold_fold.
rewrite unfold_TExpN PreTerm.exps_exp ?wf_unfold_term // map_cat unfold_exps.
rewrite map_id_in // => ? /PreTerm.in_cancel_exps pt_in. apply PreTerm.normalize_wf.
move: pt_in; rewrite mem_cat => /orP [? | /mapP [? _] ->].
- have /allP H: all PreTerm.wf_term (PreTerm.exps (unfold_term t)).
  apply PreTerm.wf_exps. apply wf_unfold_term.
  exact: H.
- apply wf_unfold_term.
Qed.

Definition is_nonce t :=
  if t is TNonce _ then true else false.

Definition is_inv t :=
  if t is TInv' _ _ then true else false.

Definition is_exp t :=
  if t is TExpN' _ _ _ then true else false.

Lemma is_nonce_unfold t : is_nonce t = PreTerm.is_nonce (unfold_term t).
Proof. by case: t => //=. Qed.

Lemma is_inv_unfold t : is_inv t = PreTerm.is_inv (unfold_term t).
Proof. by case: t => //= - []. Qed.

Lemma is_exp_unfold t : is_exp t = PreTerm.is_exp (unfold_term t).
Proof. by case: t => //= - []. Qed.

Lemma is_exp_base t : ~~ is_exp (base t).
Proof. rewrite is_exp_unfold unfold_base. apply PreTerm.base_Nexp. exact: wf_unfold_term. Qed.

Lemma base_expsK t : TExpN (base t) (exps t) = t.
Proof.
apply /unfold_term_inj; rewrite unfold_TExpN unfold_base unfold_exps.
case: (unfold_term t) (wf_unfold_term t) => //=.
move => ?? /and5P [_ ? _ /negbTE ptsN0 /andP [??]].
by rewrite /PreTerm.exp PreTerm.exps_expN //= PreTerm.cancel_exps_canceled // nilpE ptsN0
  PreTerm.base_expN // sort_le_id.
Qed.

Lemma base_exps_inj t1 t2 :
  base t1 = base t2 -> perm_eq (exps t1) (exps t2) -> t1 = t2.
Proof.
move=> eb ee; rewrite -(base_expsK t1) -(base_expsK t2) eb.
exact: TExpN_perm.
Qed.

Lemma base_expN t : ~~ is_exp t -> base t = t.
Proof.
rewrite is_exp_unfold=> tNX; apply: unfold_term_inj.
by rewrite unfold_base PreTerm.base_expN.
Qed.

Lemma exps_expN t : ~~ is_exp t -> exps t = [::].
Proof.
rewrite is_exp_unfold=> tNX; apply: (inj_map unfold_term_inj).
by rewrite unfold_exps PreTerm.exps_expN.
Qed.

Lemma is_nonce_TExpN t ts :
  is_nonce (TExpN t ts) = nilp (cancel_exps (exps t ++ ts)) && is_nonce (base t).
Proof.
rewrite !is_nonce_unfold unfold_TExpN /PreTerm.exp.
set es := PreTerm.cancel_exps _.
have -> : nilp es = nilp (cancel_exps (exps t ++ ts))
by rewrite /cancel_exps map_cat unfold_exps /nilp size_map.
case: ifP => //=. by rewrite unfold_base.
Qed.

Lemma is_nonce_TExp t1 t2 : ~~ is_exp t1 -> is_nonce (TExp t1 t2) = false.
Proof. move => ?. by rewrite is_nonce_TExpN exps_expN. Qed.

Lemma TExpNA t ts1 ts2 : TExpN (TExpN t ts1) ts2 = TExpN t (ts1 ++ ts2).
Proof.
apply: base_exps_inj; rewrite ?base_TExpN // !exps_TExpN.
rewrite perm_sort perm_sym perm_sort perm_sym.
apply perm_trans with (cancel_exps (cancel_exps (exps t ++ ts1) ++ ts2)).
- apply perm_cancel_exps. by rewrite perm_cat2r perm_sort.
- rewrite catA. apply cancel_exps_cat.
Qed.

Definition invs_canceled ts := PreTerm.invs_canceled (map unfold_term ts).

Lemma invs_canceledP ts : reflect (forall t, t \in ts -> TInv t \notin ts) (invs_canceled ts).
Proof.
apply /(iffP idP).
- move => /allP canceled t tin.
  have: (PreTerm.inv (unfold_term t) \notin (map unfold_term ts)).
  apply canceled. apply /mapP => /=. by exists t.
  apply contra => TInv_in_ts. rewrite -unfold_TInv. apply /mapP => /=. by exists (TInv t).
- move => canceled. apply /allP => /= pt /mapP [t t_in_ts ->].
  rewrite -unfold_TInv. move: (canceled t t_in_ts). apply contra.
  rewrite mem_map //. exact: unfold_term_inj.
Qed.

Lemma is_exp_TExpN t ts :
  ~~ is_exp t -> invs_canceled ts ->
  is_exp (TExpN t ts) = (ts != [::]).
Proof.
rewrite !is_exp_unfold unfold_TExpN => ??.
by rewrite PreTerm.is_exp_exp ?wf_unfold_term // -!nilpE /nilp size_map.
Qed.

Lemma is_exp_TExp t1 t2 : ~~ is_exp t1 -> is_exp (TExp t1 t2).
Proof.
move => ?. rewrite is_exp_TExpN //. apply /invs_canceledP => ?.
rewrite !inE => /eqP ->. exact: TInv_Nid.
Qed.

Lemma TExpN0 t : TExpN t [::] = t.
Proof.
rewrite unlock /= PreTerm.exp_nil.
  exact: unfold_termK.
  exact: wf_unfold_term.
Qed.

Definition tsize t := PreTerm.tsize (unfold_term t).

Lemma tsize_gt0 t : 0 < tsize t. Proof. exact: PreTerm.tsize_gt0. Qed.

Lemma tsize_TExpN t ts :
  ~~ is_exp t -> invs_canceled ts ->
  tsize (TExpN t ts)
  = (ts != [::]) + tsize t + sumn (map tsize ts).
Proof.
move => ??.
rewrite /tsize unfold_TExpN PreTerm.tsize_exp -?is_exp_unfold //.
rewrite -size_eq0 size_map size_eq0.
case: (altP eqP) => [-> | _] //=.
- by rewrite addn0.
- by rewrite big_cons /= sumnE !big_map PreTerm.base_expN // -is_exp_unfold.
Qed.

Lemma TExpN_injl : left_injective TExpN.
Proof.
move => a g1 g2 eq. apply base_exps_inj.
- by rewrite -(base_TExpN _ a) eq base_TExpN.
- rewrite -(TExpN0 g1) -(TExpN0 g2) !exps_TExpN !cats0 perm_sort perm_sym perm_sort.
  apply perm_trans with (cancel_exps (exps g2 ++ a ++ map TInv a)); rewrite perm_sym.
  + apply cancel_exps_cat_invs.
  + apply perm_trans with (cancel_exps (exps g1 ++ a ++ map TInv a)).
    * rewrite perm_sym. apply cancel_exps_cat_invs.
    * apply /perm_sort_leP. by rewrite -!exps_TExpN -!TExpNA eq.
Qed.

Lemma TExpN_injr t ts1 ts2 :
  TExpN t ts1 = TExpN t ts2 ->
  perm_eq (cancel_exps ts1) (cancel_exps ts2).
Proof.
move => /(congr1 exps). rewrite !exps_TExpN => /perm_sort_leP.
by rewrite perm_cancel_exps_catl.
Qed.

Lemma TExp_injr t t1 t2 : TExp t t1 = TExp t t2 -> t1 = t2.
Proof.
move/TExpN_injr/perm_mem/(_ t2).
by rewrite /cancel_exps /= !unfold_termK !inE eqxx => /eqP.
Qed.

Lemma tsize_eq t :
  tsize t =
  match t with
  | TInt _ => 1
  | TPair t1 t2 => S (tsize t1 + tsize t2)
  | TNonce _ => 1
  | TKey _ t => S (tsize t)
  | TSeal k t => S (tsize k + tsize t)
  | THash t => S (tsize t)
  | TExpN' pt pts _ => PreTerm.tsize (PreTerm.PTExp pt pts)
  | TInv' pt _ => PreTerm.tsize (PreTerm.PT1 O1Inv pt)
  end.
Proof. by case: t. Qed.

(*
Lemma tsize_TExpN_lt t1 ts1 t2 :
  (tsize (TExpN t1 ts1) < tsize (TExpN t1 (t2 :: ts1)))%coq_nat /\
  (tsize t2 < tsize (TExpN t1 (t2 :: ts1)))%coq_nat.
Proof.
move/ssrnat.ltP: (tsize_gt0 t1) => pos_t1.
move/ssrnat.ltP: (tsize_gt0 t2) => pos_t2.
rewrite !tsize_TExpN /= -!plusE; case: (altP eqP) => [->|ts1N0] //=; lia.
Qed.
*)

Lemma term_rect (T : term -> Type)
  (H1 : forall n, T (TInt n))
  (H2 : forall t1, T t1 ->
        forall t2, T t2 ->
        T (TPair t1 t2))
  (H3 : forall a, T (TNonce a))
  (H4 : forall kt t, T t -> T (TKey kt t))
  (H5 : forall k, T k -> forall t, T t -> T (TSeal k t))
  (H6 : forall t, T t -> T (THash t))
  (H7 : forall t, T t -> ~~ is_inv t -> T (TInv t))
  (H8 : forall t, T t -> ~~ is_exp t ->
        forall ts, foldr (fun t R => T t * R)%type unit ts ->
                   ts != [::] ->
                   sorted <=%O ts ->
                   invs_canceled ts ->
        T (TExpN t ts)) :
  forall t, T t.
Proof.
move => t; rewrite -(unfold_termK t) [fold_term]unlock.
move: (wf_unfold_term t).
elim: (unfold_term t) => {t} /=.
- by case; rewrite /fold_term_def /=.
- case; [rewrite /fold_term_def /=; auto .. |].
  move => pt IH /andP [nInv /[dup] ? /IH /H7 H].
  have: fold_term (PreTerm.PT1 O1Inv pt) = TInv (fold_term pt).
  apply unfold_term_inj.
  by rewrite unfold_TInv -PreTerm.inv_invN // !fold_termK // PreTerm.wf_inv.
  rewrite [fold_term]unlock => ->.
  apply H. rewrite -[pt]fold_termK // [fold_term]unlock in nInv. by rewrite is_inv_unfold.
- by case => [] ???? /andP [??]; rewrite /fold_term_def /=; auto.
- move => pt IHpt pts IHpts /[dup] wf_exp /and5P [wf_pt ptNexp wf_pts ptsN0 /andP [sorted_pts canceled_pts]].

case: eqP ptsN0 => //= ptsN0 _.
have [t e_pt] : {t | pt = unfold_term t}.
  by exists (fold_term pt); rewrite fold_termK.
rewrite {}e_pt {pt} in IHpt wf_pt ptNexp wf_exp *.
have [ts e_pts] : {ts | pts = map unfold_term ts}.
  exists (map fold_term pts).
  rewrite -map_comp map_id_in // => pt' pt'_pts.
  by rewrite /= fold_termK // (allP wf_pts).

  have: fold_term (PreTerm.PTExp (unfold_term t) pts) = TExpN t ts.
  apply unfold_term_inj.
  rewrite unfold_TExpN !fold_termK // -e_pts /PreTerm.exp PreTerm.base_expN //
    PreTerm.exps_expN //= PreTerm.cancel_exps_canceled // !sort_le_id //.
  move: ptsN0 => /nilP. by rewrite /nilp => /negbTE ->.
  rewrite [fold_term]unlock => ->.

  apply H8.
  - rewrite -(unfold_termK t) unlock. apply: IHpt. exact: wf_unfold_term.
  - by rewrite is_exp_unfold.
  - have -> : ts = map fold_term pts. rewrite e_pts -map_comp map_id_in //= => ?.
    by rewrite unfold_termK.
    elim: (pts) IHpts wf_pts => //= [pt' ? IH [T_pt' ?] /andP [??]]; split.
      + rewrite [fold_term]unlock. exact: T_pt'.
      + exact: IH.
  - rewrite -size_eq0 -(size_map unfold_term) -e_pts size_eq0. exact /eqP.
  - move: sorted_pts. by rewrite e_pts sorted_map.
  - by rewrite /invs_canceled -e_pts canceled_pts.
Qed.

Definition term_ind (P : term -> Prop) := @term_rect P.

Lemma term_lt_ind (T : term -> Prop) :
  (forall t, (forall t', (tsize t' < tsize t)%coq_nat -> T t') -> T t) ->
  forall t, T t.
Proof.
move=> H t.
move: {-1}(tsize t) (Nat.le_refl (tsize t)) => n.
elim: n / (lt_wf n) t => n _ IH t t_n.
apply: H => t' t'_t.
apply: (IH (tsize t')); lia.
Qed.

Lemma unfold_TExpN' t ts :
  ~~ is_exp t -> ts != [::] -> invs_canceled ts ->
  unfold_term (TExpN t ts) =
    PreTerm.PTExp (unfold_term t) (sort <=%O (map unfold_term ts)).
Proof.
move => nExp /negbTE tsN0 canceled.
rewrite unfold_TExpN /PreTerm.exp.
rewrite is_exp_unfold in nExp.
rewrite /invs_canceled in canceled.
rewrite PreTerm.exps_expN //= PreTerm.cancel_exps_canceled //.
by rewrite /nilp size_map size_eq0 tsN0 PreTerm.base_expN.
Qed.
