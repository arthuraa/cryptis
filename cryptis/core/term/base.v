From cryptis Require Import lib.
From HB Require Import structures.
From elpi.apps Require Import locker.
From mathcomp Require Import all_order all_boot.
From deriving Require Import deriving.
From Stdlib Require Import ZArith.ZArith Lia.
From iris.heap_lang Require locations.
From cryptis.core Require Export pre_term.

Import Order.POrderTheory Order.TotalTheory.

(* The three "non-free" operations — inverse, exponentiation and product — are
   represented indirectly, by a well-formed pre-term whose head is one of
   [O1Inv] / [PTExp] / [PTMul].  [is_non_free] recognises exactly those heads. *)
Definition is_non_free (pt : PreTerm.pre_term) :=
  PreTerm.is_inv pt || PreTerm.is_exp pt || PreTerm.is_mul pt.

Unset Elimination Schemes.
Inductive term :=
| TInt of Z
| TPair of term & term
| TNonce of nonce
| TKey of key_type & term
| TSeal of term & term
| THash of term
| TNonFree pt of PreTerm.wf_term pt & is_non_free pt.

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

Coercion TNonce : nonce >-> term.

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
  | TNonFree pt _ _ => pt
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
      TNonFree (PreTerm.PT1 O1Inv pt') pf isT
    else TInt 0 (*should never*)
  | PreTerm.PTExp b e =>
    if boolP (PreTerm.wf_term (PreTerm.PTExp b e)) is AltTrue pf then
      TNonFree (PreTerm.PTExp b e) pf isT
    else TInt 0 (*should never*)
  | PreTerm.PTMul ts =>
    if boolP (PreTerm.wf_term (PreTerm.PTMul ts)) is AltTrue pf then
      TNonFree (PreTerm.PTMul ts) pf isT
    else TInt 0 (*should never*)
  end.

lock Definition fold_term pt := fold_term_predef (PreTerm.normalize pt).

Lemma wf_unfold_term t : PreTerm.wf_term (unfold_term t).
Proof. by elim/term_ind': t=> //= ? -> ? ->. Qed.

Lemma wf_unfold_terms ts : all PreTerm.wf_term [seq unfold_term i | i <- ts].
Proof. elim: ts => //= ? ? ->. by rewrite wf_unfold_term. Qed.

Lemma TNonFree_irr pt (w1 w2 : PreTerm.wf_term pt) (n1 n2 : is_non_free pt) :
  TNonFree pt w1 n1 = TNonFree pt w2 n2.
Proof. by rewrite (@bool_irrelevance _ w1 w2) (@bool_irrelevance _ n1 n2). Qed.

Lemma fold_predef_NonFree {pt} (wf : PreTerm.wf_term pt) (nf : is_non_free pt) :
  fold_term_predef pt = TNonFree pt wf nf.
Proof.
case: pt wf nf => [o|[kt||] pt'|[||] b e|ts] wf nf.
1,2,3,5,6: by move: nf; rewrite /is_non_free /=.
- rewrite /=; case: (boolP (PreTerm.wf_term (PreTerm.PT1 O1Inv pt'))) => [pf'|npf];
    last by rewrite wf in npf.
  exact: TNonFree_irr.
- rewrite /=; case: (boolP (PreTerm.wf_term (PreTerm.PTExp b e))) => [pf'|npf];
    last by rewrite wf in npf.
  exact: TNonFree_irr.
- rewrite /=; case: (boolP (PreTerm.wf_term (PreTerm.PTMul ts))) => [pf'|npf];
    last by rewrite wf in npf.
  exact: TNonFree_irr.
Qed.

Lemma unfold_termK : cancel unfold_term fold_term.
Proof.
rewrite [fold_term]unlock => t.
rewrite PreTerm.normalize_wf ?wf_unfold_term //.
elim /term_ind': t => //=; try by move =>> -> // > ->.
by move => pt wf nf; apply: fold_predef_NonFree.
Qed.

Lemma unfold_fold pt : unfold_term (fold_term pt) = PreTerm.normalize pt.
Proof.
rewrite [fold_term]unlock.
have := PreTerm.wf_normalize pt. elim: (PreTerm.normalize pt) => //.
- by case.
- move => [?||] t IH wf_t; try by rewrite /= IH.
  by rewrite (fold_predef_NonFree wf_t isT).
- move => [] t1 IH1 t2 IH2 wf.
  + by move: wf; rewrite /= => /andP [??]; rewrite IH1 ?IH2.
  + by move: wf; rewrite /= => /andP [??]; rewrite IH1 ?IH2.
  + by rewrite (fold_predef_NonFree wf isT).
- by move => ts IHts wf; rewrite (fold_predef_NonFree wf isT).
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

lock Definition TInv t := fold_term (PreTerm.inv (unfold_term t)).

End TInv.

Section TExp.

lock Definition TExp b e :=
  fold_term (PreTerm.exp (unfold_term b) (unfold_term e)).

lock Definition TMulN ts :=
  fold_term (PreTerm.mul (map unfold_term ts)).

End TExp.

Definition TExpN t ts := TExp t (TMulN ts).

HB.instance Definition _ :=
  Equality.copy term (can_type unfold_termK).
HB.instance Definition _ :=
  Choice.copy term (can_type unfold_termK).
HB.instance Definition _ :=
  Countable.copy term (can_type unfold_termK).
HB.instance Definition _ : Order.Total _ term :=
  Order.CanIsTotal Order.default_display unfold_termK.

#[warnings="-projection-no-head-constant"]
HB.instance Definition _ := [isNew for seed_of_aenc_key].
HB.instance Definition _ := [Equality of aenc_key by <:].
HB.instance Definition _ := [Choice of aenc_key by <:].
HB.instance Definition _ := [Countable of aenc_key by <:].
HB.instance Definition _ := [Order of aenc_key by <:].

#[warnings="-projection-no-head-constant"]
HB.instance Definition _ := [isNew for seed_of_sign_key].
HB.instance Definition _ := [Equality of sign_key by <:].
HB.instance Definition _ := [Choice of sign_key by <:].
HB.instance Definition _ := [Countable of sign_key by <:].
HB.instance Definition _ := [Order of sign_key by <:].

#[warnings="-projection-no-head-constant"]
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
rewrite map_id_in // => _ /mapP [?? ->].
exact: normalize_unfold1.
Qed.

Lemma unfold_TInv t : unfold_term (TInv t) = PreTerm.inv (unfold_term t).
Proof.
by rewrite unlock unfold_fold PreTerm.normalize_wf // PreTerm.wf_inv // wf_unfold_term.
Qed.

Lemma unfold_TExp b e :
  unfold_term (TExp b e) = PreTerm.exp (unfold_term b) (unfold_term e).
Proof.
rewrite unlock unfold_fold PreTerm.normalize_wf => //.
by rewrite PreTerm.wf_exp //; apply wf_unfold_term.
Qed.

Lemma unfold_TMulN ts :
  unfold_term (TMulN ts) = PreTerm.mul (map unfold_term ts).
Proof.
rewrite unlock unfold_fold PreTerm.normalize_wf => //.
by rewrite PreTerm.wf_mul //; apply wf_unfold_terms.
Qed.

Lemma unfold_TExpN t ts :
  unfold_term (TExpN t ts) =
  PreTerm.exp (unfold_term t) (PreTerm.mul (map unfold_term ts)).
Proof. by rewrite /TExpN unfold_TExp unfold_TMulN. Qed.

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
  | PreTerm.PTExp b e => TExp (fold_term b) (fold_term e)
  | PreTerm.PTMul ts => TMulN (map fold_term ts)
  end.
Proof.
apply /unfold_term_inj.
case: pt => /=; try by case =>> //=; rewrite ?unfold_TInv !unfold_fold.
- by move=> [] >; rewrite /= ?unfold_TExp !unfold_fold.
- by move =>>; rewrite unfold_TMulN !unfold_fold -map_comp (eq_map unfold_fold).
Qed.

Definition base t := fold_term (PreTerm.base (unfold_term t)).
Definition exps t := map fold_term (PreTerm.exps (unfold_term t)).
Definition tfactors t := map fold_term (PreTerm.factors (unfold_term t)).

Definition is_mul t :=
  if t is TNonFree pt _ _ then PreTerm.is_mul pt else false.

Lemma is_mul_unfold t : is_mul t = PreTerm.is_mul (unfold_term t).
Proof. by case: t. Qed.

Lemma unfold_base t : unfold_term (base t) = PreTerm.base (unfold_term t).
Proof.
by rewrite /base unfold_fold PreTerm.normalize_wf //
  PreTerm.wf_base // wf_unfold_term.
Qed.

Lemma unfold_exps t :
  map unfold_term (exps t) = PreTerm.exps (unfold_term t).
Proof.
rewrite /exps -map_comp map_id_in // => pt pt_in.
apply: fold_termK.
by move/allP: (PreTerm.wf_exps (wf_unfold_term t)); apply.
Qed.

Lemma unfold_tfactors t :
  map unfold_term (tfactors t) = PreTerm.factors (unfold_term t).
Proof.
rewrite /tfactors -map_comp map_id_in // => pt pt_in.
apply: fold_termK.
by move/allP: (PreTerm.wf_factors (wf_unfold_term t)); apply.
Qed.

(* Only the identity [TMulN []] is its own inverse, so [TInv_Nid] now needs the
   term to be a non-product (all real factor-level uses are on atomic factors). *)
Lemma TInv_Nid {t} : ~~ is_mul t -> TInv t != t.
Proof.
rewrite is_mul_unfold => Nm.
by rewrite -(eqtype.inj_eq unfold_term_inj) unfold_TInv (PreTerm.inv_Nmul Nm)
  PreTerm.inv_aux_Nid.
Qed.

Lemma TInvK : involutive TInv.
Proof.
move => t; apply: unfold_term_inj.
by rewrite !unfold_TInv PreTerm.invK // wf_unfold_term.
Qed.

Lemma TInv_inj : injective TInv.
Proof. exact: inv_inj TInvK. Qed.

Lemma TMulN_perm ts1 ts2 : perm_eq ts1 ts2 -> TMulN ts1 = TMulN ts2.
Proof.
move => peq; apply: unfold_term_inj; rewrite !unfold_TMulN.
by apply: PreTerm.perm_mul; [exact: wf_unfold_terms | exact: perm_map].
Qed.

Lemma TMulN1 t : TMulN [:: t] = t.
Proof.
by apply: unfold_term_inj;
   rewrite unfold_TMulN /= (PreTerm.mul_wf1 (wf_unfold_term t)).
Qed.

Lemma TMulN_cat ts ts' : TMulN (TMulN ts :: ts') = TMulN (ts ++ ts').
Proof.
apply: unfold_term_inj; rewrite !unfold_TMulN map_cons unfold_TMulN map_cat.
by rewrite (PreTerm.mul_cat (wf_unfold_terms _) (wf_unfold_terms _)).
Qed.

Lemma TExpN_perm t ts1 ts2 : perm_eq ts1 ts2 -> TExpN t ts1 = TExpN t ts2.
Proof. by move => peq; rewrite /TExpN (@TMulN_perm _ _ peq). Qed.

Lemma TExpN_catC t ts1 ts2 : TExpN t (ts1 ++ ts2) = TExpN t (ts2 ++ ts1).
Proof. by apply: TExpN_perm; rewrite perm_catC. Qed.

Lemma base_TExp b e : base (TExp b e) = base b.
Proof.
apply: unfold_term_inj; rewrite !unfold_base unfold_TExp.
by rewrite (@PreTerm.base_exp _ _ (wf_unfold_term b)).
Qed.

Lemma base_TExpN t ts : base (TExpN t ts) = base t.
Proof. by rewrite /TExpN base_TExp. Qed.

Definition cancel_invs ts :=
  map fold_term (PreTerm.cancel_invs (map unfold_term ts)).

Lemma map_unfold_Nmul ts :
  all (fun pt => ~~ PreTerm.is_mul pt) (map unfold_term ts) =
  all (fun t => ~~ is_mul t) ts.
Proof. by rewrite all_map; apply: eq_all => t /=; rewrite is_mul_unfold. Qed.

Lemma unfold_TInv_Nmul {t} :
  ~~ is_mul t -> unfold_term (TInv t) = PreTerm.inv_aux (unfold_term t).
Proof. rewrite is_mul_unfold => Nm; by rewrite unfold_TInv (PreTerm.inv_Nmul Nm). Qed.

Lemma Nmul_TInv {t} : ~~ is_mul t -> ~~ is_mul (TInv t).
Proof.
move => Nm; rewrite is_mul_unfold (unfold_TInv_Nmul Nm).
exact: (PreTerm.is_mul_inv_aux (wf_unfold_term t)).
Qed.

Lemma perm_cancel_invs ts1 ts2 :
  all (fun t => ~~ is_mul t) ts1 ->
  perm_eq ts1 ts2 -> perm_eq (cancel_invs ts1) (cancel_invs ts2).
Proof.
move => Nm1 peq. rewrite /cancel_invs.
apply perm_map; apply PreTerm.perm_cancel_invs;
  [exact: wf_unfold_terms | exact: perm_map].
Qed.

Lemma cancel_invs_subseq ts : subseq (cancel_invs ts) ts.
Proof.
rewrite /cancel_invs.
apply: subseq_trans. apply map_subseq. apply PreTerm.cancel_invs_subseq.
by rewrite (mapK unfold_termK).
Qed.

Lemma mem_cancel_invs ts : { subset cancel_invs ts <= ts }.
Proof. apply mem_subseq. exact: cancel_invs_subseq. Qed.

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
  ~~ is_mul t -> all (fun t => ~~ is_mul t) ts ->
  count_mem t (cancel_invs ts) = count_mem t ts - count_mem (TInv t) ts.
Proof.
move => Nmt Nm.
have Nmt' : ~~ PreTerm.is_mul (unfold_term t) by rewrite -is_mul_unfold.
have Nm' : all (fun pt => ~~ PreTerm.is_mul pt) (map unfold_term ts)
  by rewrite map_unfold_Nmul.
rewrite /cancel_invs count_map_fold ?PreTerm.wf_cancel_invs ?wf_unfold_terms //.
rewrite PreTerm.count_cancel // ?wf_unfold_term // ?wf_unfold_terms //.
by rewrite -(unfold_TInv_Nmul Nmt) !count_map.
Qed.

Lemma count_perm_cancel {ts1 ts2} :
  all (fun t => ~~ is_mul t) ts1 -> all (fun t => ~~ is_mul t) ts2 ->
  (forall t, ~~ is_mul t ->
        count_mem t ts1 - count_mem (TInv t) ts1 =
        count_mem t ts2 - count_mem (TInv t) ts2) <->
  perm_eq (cancel_invs ts1) (cancel_invs ts2).
Proof.
move => Nm1 Nm2; split.
- move => wt_eq. apply /allP => /= t; rewrite mem_cat => /orP t_in.
  have Nmt : ~~ is_mul t.
    case: t_in => /mem_cancel_invs h;
      [exact: (allP Nm1 _ h) | exact: (allP Nm2 _ h)].
  by rewrite !count_cancel // wt_eq.
- move => peq t Nmt. rewrite -!count_cancel //. exact: (elimT permP peq).
Qed.

Lemma count_perm_cancel_redux {ts1 ts2} :
  all (fun t => ~~ is_mul t) ts1 -> all (fun t => ~~ is_mul t) ts2 ->
  (forall t, ~~ is_mul t ->
        count_mem t ts1 + count_mem (TInv t) ts2 =
        count_mem t ts2 + count_mem (TInv t) ts1) <->
  perm_eq (cancel_invs ts1) (cancel_invs ts2).
Proof.
move => Nm1 Nm2; rewrite -(count_perm_cancel Nm1 Nm2) !addnE !subnE.
split => H t Nmt; have := H t Nmt; first lia.
have := H (TInv t) (Nmul_TInv Nmt); rewrite TInvK. lia.
Qed.

Lemma count_TInv_cancel {t ts} :
  ~~ is_mul t -> all (fun t => ~~ is_mul t) ts ->
  count_mem t (cancel_invs ts) != 0 -> count_mem (TInv t) (cancel_invs ts) == 0.
Proof.
move => Nmt Nm.
by rewrite !count_cancel ?(Nmul_TInv Nmt) // TInvK -ltnNge => /ltnW.
Qed.

Lemma cancel_invs_cat ts1 ts2 :
  all (fun t => ~~ is_mul t) ts1 -> all (fun t => ~~ is_mul t) ts2 ->
  perm_eq (cancel_invs (cancel_invs ts1 ++ ts2))
          (cancel_invs (ts1 ++ ts2)).
Proof.
move => Nm1 Nm2.
have Nmc1 : all (fun t => ~~ is_mul t) (cancel_invs ts1).
  by apply/allP => t /mem_cancel_invs h; exact: (allP Nm1 _ h).
apply count_perm_cancel; rewrite ?all_cat ?Nmc1 ?Nm1 ?Nm2 //.
move => t Nmt. rewrite !count_cat.
case: (count_mem t (cancel_invs ts1) =P 0)
    => /eqP => [| /(count_TInv_cancel Nmt Nm1)];
      rewrite !count_cancel ?(Nmul_TInv Nmt) // TInvK => /[dup] ? /eqP ->;
      rewrite add0n !subnDA.
- by rewrite addnC subnBA.
- by rewrite addnBAC.
Qed.

Lemma perm_cancel_invs_catl ts1 ts2 ts :
  all (fun t => ~~ is_mul t) ts1 -> all (fun t => ~~ is_mul t) ts2 ->
  all (fun t => ~~ is_mul t) ts ->
  perm_eq (cancel_invs (ts ++ ts1)) (cancel_invs (ts ++ ts2)) =
  perm_eq (cancel_invs ts1) (cancel_invs ts2).
Proof.
move => Nm1 Nm2 Nm.
have Ntts1 : all (fun t => ~~ is_mul t) (ts ++ ts1) by rewrite all_cat Nm Nm1.
have Ntts2 : all (fun t => ~~ is_mul t) (ts ++ ts2) by rewrite all_cat Nm Nm2.
apply /(sameP idP); apply /(iffP idP) => H.
- apply/(count_perm_cancel_redux Ntts1 Ntts2) => t Nmt.
  have := (proj2 (count_perm_cancel_redux Nm1 Nm2) H) t Nmt.
  rewrite !count_cat !addnE; lia.
- apply/(count_perm_cancel_redux Nm1 Nm2) => t Nmt.
  have := (proj2 (count_perm_cancel_redux Ntts1 Ntts2) H) t Nmt.
  rewrite !count_cat !addnE; lia.
Qed.

Lemma count_map_TInv t ts:
  count_mem t (map TInv ts) = count_mem (TInv t) ts.
Proof. elim: ts => //= [?? ->]. by rewrite (inv_eq TInvK). Qed.

Lemma cancel_invs_cat_invs ts1 ts2 :
  all (fun t => ~~ is_mul t) ts1 -> all (fun t => ~~ is_mul t) ts2 ->
  perm_eq (cancel_invs (ts1 ++ ts2 ++ map TInv ts2)) (cancel_invs ts1).
Proof.
move => Nm1 Nm2.
have NmT2 : all (fun t => ~~ is_mul t) (map TInv ts2).
  by apply/allP => t /mapP [s /(allP Nm2) Nms ->]; exact: Nmul_TInv.
apply count_perm_cancel; rewrite ?all_cat ?Nm1 ?Nm2 ?NmT2 //.
move => t Nmt. rewrite !count_cat !count_map_TInv /= TInvK !addnE !subnE. lia.
Qed.

Lemma unfold_cancel_invs ts :
  map unfold_term (cancel_invs ts) = PreTerm.cancel_invs (map unfold_term ts).
Proof.
rewrite /cancel_invs -map_comp map_id_in // => pt pt_in.
apply: fold_termK.
by move/allP: (PreTerm.wf_cancel_invs (wf_unfold_terms ts)); apply.
Qed.

Lemma unfold_sort s :
  map unfold_term (sort <=%O s) = sort <=%O (map unfold_term s).
Proof. by rewrite sort_map. Qed.

Lemma exps_TExpN t ts :
  all (fun t => ~~ is_mul t) ts ->
  exps (TExpN t ts) = sort <=%O (cancel_invs (exps t ++ ts)).
Proof.
move => atom.
have atomU : all (fun pt => ~~ PreTerm.is_mul pt) [seq unfold_term i | i <- ts].
  rewrite all_map; apply/allP => t' t'ts /=.
  by rewrite -is_mul_unfold; move/allP: atom; apply.
apply: (inj_map unfold_term_inj).
rewrite unfold_exps unfold_TExpN.
rewrite (PreTerm.exps_exp (wf_unfold_term t)
          (PreTerm.wf_mul (wf_unfold_terms ts))).
rewrite (PreTerm.factors_mul (wf_unfold_terms ts))
        (PreTerm.flatten_factors_Nmul_id atomU).
rewrite unfold_sort unfold_cancel_invs map_cat unfold_exps.
by rewrite (PreTerm.sortcancel_catr
             (PreTerm.wf_exps (wf_unfold_term t))
             (PreTerm.Nmul_factors (PreTerm.wf_expo (wf_unfold_term t)))
             (wf_unfold_terms ts) atomU).
Qed.

Definition is_nonce t :=
  if t is TNonce _ then true else false.

Definition is_inv t :=
  if t is TNonFree pt _ _ then PreTerm.is_inv pt else false.

Definition is_exp t :=
  if t is TNonFree pt _ _ then PreTerm.is_exp pt else false.

Lemma is_nonce_unfold t : is_nonce t = PreTerm.is_nonce (unfold_term t).
Proof. by case: t => //= pt _ nf; move: nf; case: pt. Qed.

Lemma is_inv_unfold t : is_inv t = PreTerm.is_inv (unfold_term t).
Proof. by case: t. Qed.

Lemma is_inv_TInv t : ~~ is_mul t -> is_inv (TInv t) = ~~ is_inv t.
Proof.
move => Nm; rewrite !is_inv_unfold (unfold_TInv_Nmul Nm).
have := wf_unfold_term t.
case: (unfold_term t) => //. by case => //= ? /and3P [/negbTE ? _ _].
Qed.

Lemma is_exp_unfold t : is_exp t = PreTerm.is_exp (unfold_term t).
Proof. by case: t. Qed.

Lemma is_exp_base t : ~~ is_exp (base t).
Proof. rewrite is_exp_unfold unfold_base. apply PreTerm.base_Nexp. exact: wf_unfold_term. Qed.

Lemma is_exp_TInv t : ~~ is_mul t -> ~~ is_inv t -> ~~ is_exp (TInv t).
Proof.
move => Nm; rewrite is_inv_unfold => ?.
by rewrite is_exp_unfold (unfold_TInv_Nmul Nm) PreTerm.inv_invN.
Qed.

Lemma base_expsK t : TExpN (base t) (exps t) = t.
Proof.
apply/unfold_term_inj; rewrite unfold_TExpN unfold_base unfold_exps /PreTerm.exps.
rewrite (PreTerm.mul_factors (PreTerm.wf_expo (wf_unfold_term t))).
exact: (PreTerm.exp_base_expo (wf_unfold_term t)).
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

Lemma is_nonce_TExp t1 t2 : ~~ is_exp t1 -> ~~ is_mul t2 -> ~~ is_nonce (TExp t1 t2).
Proof.
move => Nx1 Nm2.
rewrite is_exp_unfold in Nx1; rewrite is_mul_unfold in Nm2.
rewrite is_nonce_unfold unfold_TExp /PreTerm.exp (PreTerm.expo_expN Nx1).
have -> : PreTerm.mul [:: PreTerm.PTMul [::]; unfold_term t2] = unfold_term t2.
  have -> : PreTerm.mul [:: PreTerm.PTMul [::]; unfold_term t2]
          = PreTerm.mul [:: unfold_term t2] by rewrite /PreTerm.mul /= !cats0.
  exact: PreTerm.mul_wf1 (wf_unfold_term t2).
have -> : (unfold_term t2 == PreTerm.PTMul [::]) = false.
  by apply/negbTE; apply: contra Nm2 => /eqP ->.
by [].
Qed.

Lemma TExpNA t ts1 ts2 : TExpN (TExpN t ts1) ts2 = TExpN t (ts1 ++ ts2).
Proof.
rewrite /TExpN; apply: unfold_term_inj.
rewrite !unfold_TExp !unfold_TMulN.
rewrite (PreTerm.expA (wf_unfold_term t)
          (PreTerm.wf_mul (wf_unfold_terms ts1)) (PreTerm.wf_mul (wf_unfold_terms ts2))).
by rewrite (PreTerm.mul_mul2 (wf_unfold_terms ts1) (wf_unfold_terms ts2)) map_cat.
Qed.

Lemma TExpNC : right_commutative TExpN.
Proof. by move =>>; rewrite !TExpNA TExpN_catC. Qed.

Definition invs_canceled ts := PreTerm.invs_canceled (map unfold_term ts).

Definition atomic (ts : seq term) : bool := all (fun t => ~~ is_mul t) ts.

Definition wf_mul_list (ts : seq term) : bool :=
  [&& atomic ts, sorted <=%O ts, invs_canceled ts & size ts != 1].

Lemma atomic_unfold ts :
  atomic ts -> all (fun pt => ~~ PreTerm.is_mul pt) (map unfold_term ts).
Proof.
rewrite /atomic => /allP H; rewrite all_map; apply/allP => x x_ts.
by rewrite /= -is_mul_unfold; apply: H.
Qed.

Lemma wf_mul_list_unfold ts :
  wf_mul_list ts -> PreTerm.wf_term (PreTerm.PTMul (map unfold_term ts)).
Proof.
case/and4P => atom sort canc szN1.
apply/and5P; split.
- exact: wf_unfold_terms.
- exact: atomic_unfold.
- by rewrite sorted_map.
- exact: canc.
- by rewrite size_map.
Qed.

(* Characterisation of the (real-[inv]) [invs_canceled] at the term level: a
   factor list is canceled iff no factor's *distributing* inverse [TInv] is also
   in the list.  Unconditional now — [invs_canceled] is defined via [PreTerm.inv]
   (the real inverse), so [unfold_TInv] (which needs no side condition) bridges it
   directly, no atomicity required. *)
Lemma invs_canceledE ts : invs_canceled ts = all (fun t => TInv t \notin ts) ts.
Proof.
rewrite /invs_canceled /PreTerm.invs_canceled all_map.
apply: eq_all => t /=.
by rewrite -unfold_TInv (mem_map unfold_term_inj).
Qed.

(* [TMulN []] (the multiplicative identity) is the unique self-inverse term. *)
Lemma TInv_fixed t : (TInv t == t) = (t == TMulN [::]).
Proof.
apply/idP/idP.
- move=> /eqP E; apply/eqP/unfold_term_inj; rewrite unfold_TMulN /=.
  move: E => /(congr1 unfold_term); rewrite unfold_TInv => /eqP.
  by rewrite (PreTerm.inv_fixed (wf_unfold_term t)) => /eqP.
- by move=> /eqP ->; apply/eqP/unfold_term_inj; rewrite unfold_TInv unfold_TMulN /=.
Qed.

Lemma invs_canceledP {ts} :
  reflect (forall t, t \in ts -> TInv t \notin ts) (invs_canceled ts).
Proof. rewrite invs_canceledE; exact: allP. Qed.

(* Permutation-invariance of [invs_canceled] holds universally: it is [all] of a
   membership test, and both are stable under permutation (no atomicity needed). *)
Lemma perm_invs_canceled ts1 ts2 :
  perm_eq ts1 ts2 -> invs_canceled ts1 = invs_canceled ts2.
Proof.
move => peq.
rewrite !invs_canceledE (perm_all (fun t => TInv t \notin ts1) peq).
by apply: eq_all => t; rewrite (perm_mem peq).
Qed.

(* A singleton cancels iff it is not the identity ([TInv (TMulN []) = TMulN []]). *)
Lemma invs_canceled1 t : invs_canceled [:: t] = (t != TMulN [::]).
Proof. by rewrite invs_canceledE /= andbT inE TInv_fixed. Qed.

(* The identity [TMulN []] is a product, so no atomic term equals it. *)
Lemma Nmul_neq_unit {t} : ~~ is_mul t -> t != TMulN [::].
Proof. by apply: contra => /eqP ->; rewrite is_mul_unfold unfold_TMulN. Qed.

(* Atomic terms are never the identity, so a single atomic factor always cancels. *)
Lemma invs_canceled_Nmul1 {t} : ~~ is_mul t -> invs_canceled [:: t].
Proof. by move=> Nm; rewrite invs_canceled1; exact: Nmul_neq_unit. Qed.

Lemma all_TInv_neq (t : term) us : all (fun t' => TInv t' != t) us = (TInv t \notin us).
Proof.
rewrite (eq_all (a2 := fun t' => t' != TInv t)); last first.
  by move=> t' /=; rewrite (inv_eq TInvK).
by rewrite -has_pred1 -all_predC.
Qed.

Lemma invs_canceled_cons {t ts} :
  ~~ is_mul t ->
  invs_canceled (t :: ts) = (TInv t \notin ts) && invs_canceled ts.
Proof.
move=> Nm; rewrite !invs_canceledE /= inE (negbTE (TInv_Nid Nm)) /=.
under eq_in_all => t' t'_us do rewrite inE negb_or.
by rewrite all_predI all_TInv_neq -invs_canceledE andbA andbb.
Qed.

Lemma invs_canceled2 t1 t2 :
  invs_canceled [:: t1 ; t2] = (TInv t1 != t2) && (TMulN [::] \notin [:: t1; t2]).
Proof.
rewrite invs_canceledE /= !inE !negb_or andbT !TInv_fixed.
have -> : (TInv t2 != t1) = (TInv t1 != t2) by rewrite [TInv t2 == t1]eq_sym (inv_eq TInvK).
rewrite [TMulN [::] == t1]eq_sym [TMulN [::] == t2]eq_sym.
by case: (t1 != TMulN [::]); case: (TInv t1 != t2); case: (t2 != TMulN [::]).
Qed.

Lemma invs_canceled2_Nmul {t1 t2} :
  ~~ is_mul t1 -> ~~ is_mul t2 ->
  invs_canceled [:: t1 ; t2] = (t1 != TInv t2).
Proof.
move=> Nm1 Nm2; rewrite invs_canceled2 (inv_eq TInvK) !inE negb_or.
rewrite [TMulN [::] == t1]eq_sym [TMulN [::] == t2]eq_sym.
by rewrite (Nmul_neq_unit Nm1) (Nmul_neq_unit Nm2) !andbT.
Qed.

Lemma parity_cancel_invs ts : odd (size (cancel_invs ts)) = odd (size ts).
Proof. by rewrite /cancel_invs size_map PreTerm.parity_cancel_invs size_map. Qed.

Lemma invs_canceled_exps t : invs_canceled (exps t).
Proof. by rewrite /invs_canceled unfold_exps PreTerm.invs_canceled_exps // wf_unfold_term. Qed.

Lemma exps_Nmul t' t : t' \in exps t -> ~~ is_mul t'.
Proof.
move => t'_t; rewrite is_mul_unfold.
move: (PreTerm.Nmul_factors (PreTerm.wf_expo (wf_unfold_term t))) => /allP H.
apply: H; rewrite -/(PreTerm.exps (unfold_term t)) -unfold_exps.
exact: map_f.
Qed.

Lemma atom_exps t : all (fun t => ~~ is_mul t) (exps t).
Proof. by apply/allP => t' t't; exact: exps_Nmul t't. Qed.

Lemma invs_canceled_cons_exps {t1} t2 :
  ~~ is_mul t1 ->
  invs_canceled (t1 :: exps t2) = (TInv t1 \notin exps t2).
Proof.
by move => Nm; rewrite (invs_canceled_cons Nm) invs_canceled_exps andbT.
Qed.

(* [cancel_invs] leaves a canonical *atomic* list unchanged.  Atomicity is
   required: the (factor-level) [cancel_invs] would still cancel a product and its
   [inv_aux]-wrapper even when the list is [invs_canceled] w.r.t. the real inverse. *)
Lemma cancel_invs_canceled ts :
  atomic ts -> invs_canceled ts -> cancel_invs ts = ts.
Proof.
move=> atom canc.
have atomU : all (fun pt => ~~ PreTerm.is_mul pt) (map unfold_term ts).
  rewrite all_map; apply/allP => t' t'ts /=; rewrite -is_mul_unfold.
  by move/allP: atom; apply.
by rewrite /cancel_invs (PreTerm.cancel_invs_canceled atomU) ?(mapK unfold_termK).
Qed.

Lemma cancel_invs_exps t : cancel_invs (exps t) = exps t.
Proof. apply: cancel_invs_canceled; [exact: atom_exps | exact: invs_canceled_exps]. Qed.

Lemma cancel_invs1 t : cancel_invs [:: t] = [:: t].
Proof. by rewrite /cancel_invs /= unfold_termK. Qed.

Lemma invs_canceled_count {t} ts :
  invs_canceled ts ->
  count_mem t ts - count_mem (TInv t) ts = count_mem t ts.
Proof.
move=> can_ts.
have [t_ts|/count_memPn -> //] := boolP (t \in ts).
suff -> : count_mem (TInv t) ts = 0 by rewrite subn0.
apply/count_memPn.
by move: can_ts; rewrite invs_canceledE => /allP/(_ _ t_ts).
Qed.

Lemma is_exp_TExpN t ts :
  ~~ is_exp t -> all (fun t => ~~ is_mul t) ts -> invs_canceled ts ->
  is_exp (TExpN t ts) = (ts != [::]).
Proof.
move => Nxt atom canc.
have atomU : all (fun pt => ~~ PreTerm.is_mul pt) (map unfold_term ts).
  rewrite all_map; apply/allP => t' t'ts /=; rewrite -is_mul_unfold.
  by move/allP: atom; apply.
rewrite /TExpN is_exp_unfold unfold_TExp.
rewrite (@PreTerm.is_exp_exp _ _ (wf_unfold_term t)).
rewrite (PreTerm.expo_expN _); last by rewrite -is_exp_unfold.
rewrite unfold_TMulN -[PreTerm.PTMul [::]]/(PreTerm.mul [::]).
rewrite (PreTerm.mul_mul2 (ts1 := [::]) isT (wf_unfold_terms ts)) /=.
rewrite (PreTerm.mul_eq_unit atomU canc).
by case: ts {atom canc atomU}.
Qed.

Lemma is_exp_TExp t1 t2 : ~~ is_exp t1 -> ~~ is_mul t2 -> is_exp (TExp t1 t2).
Proof.
move => Nx1 Nm2.
have -> : TExp t1 t2 = TExpN t1 [:: t2] by rewrite /TExpN TMulN1.
have atom : all (fun t => ~~ is_mul t) [:: t2] by rewrite /= Nm2.
by rewrite (@is_exp_TExpN t1 [:: t2] Nx1 atom (invs_canceled_Nmul1 Nm2)).
Qed.

Lemma TExpN0 : right_id [::] TExpN.
Proof.
move => t; rewrite /TExpN; apply: unfold_term_inj.
rewrite unfold_TExp unfold_TMulN /=.
by rewrite (PreTerm.exp_unit (wf_unfold_term t)).
Qed.

Definition tsize t := PreTerm.tsize (unfold_term t).

Lemma tsize_gt0 t : 0 < tsize t. Proof. exact: PreTerm.tsize_gt0. Qed.

Lemma tsize_eq t :
  tsize t =
  match t with
  | TInt _ => 1
  | TPair t1 t2 => S (tsize t1 + tsize t2)
  | TNonce _ => 1
  | TKey _ t => S (tsize t)
  | TSeal k t => S (tsize k + tsize t)
  | THash t => S (tsize t)
  | TNonFree pt _ _ => PreTerm.tsize pt
  end.
Proof. by case: t. Qed.

Lemma tsize_TInv t : ~~ is_mul t -> ~~ is_inv t -> tsize (TInv t) = S (tsize t).
Proof.
move => Nm ?.
by rewrite /tsize (unfold_TInv_Nmul Nm) PreTerm.tsize_inv -?is_inv_unfold.
Qed.

Lemma tsize_TExp t1 t2 :
  ~~ is_exp t1 -> ~~ is_mul t2 -> tsize (TExp t1 t2) = S (tsize t1 + tsize t2).
Proof.
move => Nx1 Nm2.
rewrite is_exp_unfold in Nx1; rewrite is_mul_unfold in Nm2.
have neq : unfold_term t2 != PreTerm.PTMul [::] by apply: contra Nm2 => /eqP ->.
by rewrite /tsize unfold_TExp (PreTerm.tsize_exp_Nexp Nx1 (wf_unfold_term t2) neq).
Qed.

Definition tsizeE := (tsize_TInv, tsize_TExp, tsize_eq).

Lemma TExpNK ts t :
  all (fun t => ~~ is_mul t) ts -> all (fun t => ~~ is_mul t) (map TInv ts) ->
  TExpN (TExpN t ts) (map TInv ts) = t.
Proof.
move => atom atomInv.
rewrite TExpNA /TExpN.
have -> : TMulN (ts ++ map TInv ts) = TMulN [::].
  apply: unfold_term_inj; rewrite !unfold_TMulN map_cat.
  have -> : map unfold_term (map TInv ts) = map PreTerm.inv_aux (map unfold_term ts).
    rewrite -!map_comp; apply/eq_in_map => x x_ts /=.
    exact: unfold_TInv_Nmul (allP atom _ x_ts).
  apply: PreTerm.mul_invs; first exact: wf_unfold_terms.
  rewrite all_cat; apply/andP; split.
    rewrite all_map; apply/allP => t' t'ts /=; rewrite -is_mul_unfold.
    by move/allP: atom; apply.
  rewrite -map_comp; apply/allP => pt /mapP [t' t'ts ->] /=.
  rewrite -(unfold_TInv_Nmul (allP atom _ t'ts)) -is_mul_unfold.
  by move/allP: atomInv; apply; rewrite (map_f TInv).
by apply: unfold_term_inj;
   rewrite unfold_TExp unfold_TMulN /= (PreTerm.exp_unit (wf_unfold_term t)).
Qed.

Lemma TExpK' t1 t2 :
  ~~ is_mul (TInv t2) -> ~~ is_mul t2 ->
  TExp (TExp t1 (TInv t2)) t2 = t1.
Proof.
move => NmI2 Nm2.
have atom : all (fun t => ~~ is_mul t) [:: TInv t2] by rewrite /= NmI2.
have atomInv : all (fun t => ~~ is_mul t) (map TInv [:: TInv t2]) by rewrite /= TInvK Nm2.
move: (@TExpNK [:: TInv t2] t1 atom atomInv) => H.
by rewrite /= TInvK /TExpN !TMulN1 in H.
Qed.

Lemma in_TInv_exps t1 t2 : t1 \in exps t2 -> TInv t1 \notin exps t2.
Proof.
move: (invs_canceled_exps t2) => /invs_canceledP H.
exact: H.
Qed.

Lemma in_TInv_expsV t1 t2 : TInv t1 \in exps t2 -> t1 \notin exps t2.
Proof. by rewrite -{2}[t1]TInvK; exact: in_TInv_exps. Qed.

Lemma in_exps_TInv t1 t2 : (t1 \notin exps t2) || (TInv t1 \notin exps t2).
Proof. by have [/in_TInv_exps ->|] := boolP (t1 \in _). Qed.

Lemma tsize_lt_TInv {t} : ~~ is_mul t -> tsize (TInv t) <= S (tsize t).
Proof.
move => Nm; have NmT := Nmul_TInv Nm.
have [inv_t|ninv_t] := boolP (is_inv t).
- rewrite -{2}[t]TInvK [tsize (TInv (TInv _))]tsizeE ?is_inv_TInv ?negbK //.
  apply/ssrnat.leP; lia.
- rewrite tsizeE //.
Qed.

Lemma TExp_expsE t1 t2 : TExp t1 t2 = TExpN (base t1) (exps t1 ++ [:: t2]).
Proof. by rewrite -{1}(base_expsK t1) -TExpNA /TExpN TMulN1. Qed.

Lemma tsize_TExpN t ts :
  ~~ is_exp t -> all (fun t => ~~ is_mul t) ts -> invs_canceled ts ->
  tsize (TExpN t ts) =
  (ts != [::]) + (1 < size ts) + tsize t + sumn (map tsize ts).
Proof.
move => Nxt atom canc.
have atomU : all (fun pt => ~~ PreTerm.is_mul pt) (map unfold_term ts).
  rewrite all_map; apply/allP => t' t'ts /=; rewrite -is_mul_unfold.
  by move/allP: atom; apply.
have [->|tsN0] := eqVneq ts [::].
  have -> : TExpN t [::] = t.
    apply: unfold_term_inj; rewrite /TExpN unfold_TExp unfold_TMulN /=.
    by rewrite (PreTerm.exp_unit (wf_unfold_term t)).
  by rewrite /= !add0n addn0.
have eneq : PreTerm.mul (map unfold_term ts) != PreTerm.PTMul [::].
  by rewrite (PreTerm.mul_eq_unit atomU canc) -size_eq0 size_map size_eq0.
have sumeq : sumn [seq PreTerm.tsize pt | pt <- map unfold_term ts] = sumn (map tsize ts).
  by rewrite -map_comp.
rewrite [tsize (TExpN t ts)]/tsize /TExpN unfold_TExp unfold_TMulN.
rewrite (PreTerm.tsize_exp_Nexp _ (PreTerm.wf_mul (wf_unfold_terms ts)) eneq);
  last by rewrite -is_exp_unfold.
rewrite (PreTerm.tsize_mul atomU canc); last by rewrite -size_eq0 size_map size_eq0.
rewrite size_map sumeq -[PreTerm.tsize (unfold_term t)]/(tsize t) /=.
by rewrite !addnE; lia.
Qed.

Lemma tsize_lt_TExp_strong t1 t2 :
  ~~ is_mul t2 -> TInv t2 \notin exps t1 ->
  tsize t1 < tsize (TExp t1 t2) /\
  S (tsize t2) < tsize (TExp t1 t2).
Proof.
move => Nm2 t2_t1.
have atom : all (fun t => ~~ is_mul t) (exps t1 ++ [:: t2]).
  by rewrite all_cat (atom_exps t1) /= Nm2.
have canc : invs_canceled (exps t1 ++ [:: t2]).
  have pperm : perm_eq (exps t1 ++ [:: t2]) (t2 :: exps t1) by rewrite -cat1s perm_catC.
  rewrite (@perm_invs_canceled _ _ pperm).
  by rewrite (invs_canceled_cons Nm2) t2_t1 (invs_canceled_exps t1).
have e1 : tsize t1 = (exps t1 != [::]) + (1 < size (exps t1)) + tsize (base t1)
                     + sumn (map tsize (exps t1)).
  by rewrite -{1}(base_expsK t1)
     (@tsize_TExpN (base t1) (exps t1) (is_exp_base t1) (atom_exps t1)
        (invs_canceled_exps t1)).
rewrite TExp_expsE (@tsize_TExpN (base t1) (exps t1 ++ [:: t2]) (is_exp_base t1) atom canc).
rewrite map_cat size_cat sumn_cat /= e1 !addn0 addn1.
have /ssrnat.ltP g1 := tsize_gt0 (base t1).
have /ssrnat.ltP g2 := tsize_gt0 t2.
rewrite (_ : (exps t1 != [::]) = (0 < size (exps t1))); last by rewrite lt0n size_eq0.
rewrite (_ : (exps t1 ++ [:: t2] != [::]) = true); last by case: (exps t1).
by split; apply/ssrnat.ltP;
   case: (size (exps t1)) => [|[|n]]; rewrite /= ?addn0 ?add0n !addnE; lia.
Qed.

Lemma tsize_lt_TExp t1 t2 :
  ~~ is_mul t2 -> TInv t2 \notin exps t1 ->
  tsize t1 < tsize (TExp t1 t2) /\
  tsize (TInv t2) < tsize (TExp t1 t2) /\
  tsize t2 < tsize (TExp t1 t2).
Proof.
move => Nm2 t2_t1; case: (@tsize_lt_TExp_strong t1 t2 Nm2 t2_t1) => /ssrnat.ltP H1 /ssrnat.ltP H2.
have /ssrnat.leP ? := tsize_lt_TInv Nm2.
do !split; apply/ssrnat.ltP; lia.
Qed.

Lemma TExpN_injr t ts1 ts2 :
  all (fun t => ~~ is_mul t) ts1 -> all (fun t => ~~ is_mul t) ts2 ->
  TExpN t ts1 = TExpN t ts2 ->
  perm_eq (cancel_invs ts1) (cancel_invs ts2).
Proof.
move => atom1 atom2 /(congr1 exps).
rewrite (@exps_TExpN t ts1 atom1) (@exps_TExpN t ts2 atom2) => /perm_sort_leP.
by rewrite (@perm_cancel_invs_catl ts1 ts2 (exps t) atom1 atom2 (atom_exps t)).
Qed.

Lemma TExp_injr t t1 t2 :
  ~~ is_mul t1 -> ~~ is_mul t2 -> TExp t t1 = TExp t t2 -> t1 = t2.
Proof.
move => Nm1 Nm2 e.
have e' : TExpN t [:: t1] = TExpN t [:: t2] by rewrite /TExpN !TMulN1.
have a1 : all (fun t => ~~ is_mul t) [:: t1] by rewrite /= Nm1.
have a2 : all (fun t => ~~ is_mul t) [:: t2] by rewrite /= Nm2.
move: (@TExpN_injr t [:: t1] [:: t2] a1 a2 e') => /perm_mem /(_ t2).
by rewrite !cancel_invs1 !inE eqxx => /eqP.
Qed.

Definition count_exp_nat t1 t2 := count_mem t1 (exps t2).

Lemma count_exp_nat_eq0 t1 t2 : t1 \notin exps t2 -> count_exp_nat t1 t2 = 0.
Proof. move=> t1V_t2; exact/count_memPn. Qed.

Lemma count_exp_nat_gt0 t1 t2 : (count_exp_nat t1 t2 > 0) = (t1 \in exps t2).
Proof. by rewrite /count_exp_nat -has_count has_pred1. Qed.

Lemma count_exp_nat_TExp t1 t2 t3 :
  ~~ is_mul t3 ->
  count_exp_nat t1 (TExp t2 t3) =
  if t1 == TInv t3 then (count_exp_nat t1 t2).-1
  else if t1 == t3 then (count_exp_nat t1 t2).+1 - (TInv t1 \in exps t2)
  else count_exp_nat t1 t2.
Proof.
move => Nm3.
have [Mt1|Nmt1] := boolP (is_mul t1).
  have z : forall X, count_mem t1 (exps X) = 0.
    by move => X; apply/count_memPn/negP => /exps_Nmul H; rewrite Mt1 in H.
  rewrite /count_exp_nat !z.
  have -> : (t1 == TInv t3) = false.
    by apply/negP => /eqP e; move: Mt1; rewrite e (negbTE (Nmul_TInv Nm3)).
  have -> : (t1 == t3) = false.
    by apply/negP => /eqP e; move: Mt1; rewrite e (negbTE Nm3).
  by [].
have atom : all (fun t => ~~ is_mul t) ([:: t3] ++ exps t2).
  by rewrite all_cat /= Nm3 (atom_exps t2).
rewrite /count_exp_nat TExp_expsE TExpN_catC.
rewrite (@exps_TExpN (base t2) ([:: t3] ++ exps t2) atom).
rewrite (@exps_expN (base t2) (is_exp_base t2)) cat0s count_sort.
rewrite (@count_cancel t1 ([:: t3] ++ exps t2) Nmt1 atom) /=.
rewrite -![count_mem _ _]/(count_exp_nat _ _).
rewrite ![t3 == _]eq_sym (can2_eq TInvK TInvK).
case: (t1 =P t3) => [<-|t1_t3] /=.
  rewrite [_ == TInv _]eq_sym (negbTE (TInv_Nid Nmt1)) /= add0n add1n.
  have [t1_t2|t1_t2] := boolP (TInv t1 \in exps t2); last first.
    by rewrite (count_exp_nat_eq0 _ _ t1_t2).
  rewrite count_exp_nat_eq0 1?in_TInv_expsV //.
  by move: t1_t2; rewrite -count_exp_nat_gt0; case: count_exp_nat.
case: (t1 =P TInv t3) => [t1E|t1_t3V] /=.
  by rewrite add0n add1n subnS
     (invs_canceled_count (exps t2) (invs_canceled_exps t2)).
by rewrite !add0n (invs_canceled_count (exps t2) (invs_canceled_exps t2)).
Qed.

Variant count_exp_nat_TExp_spec t1 t2 t3 : nat -> Type :=
| CountExpTExpSame0
  of t1 = t3 & TInv t3 \in exps t2
: count_exp_nat_TExp_spec t1 t2 t3 0

| CountExpTExpSame1
  of t1 = t3 & TInv t3 \notin exps t2
: count_exp_nat_TExp_spec t1 t2 t3 (count_exp_nat t1 t2).+1

| CountExpTExpTInv
  of t1 = TInv t3
: count_exp_nat_TExp_spec t1 t2 t3 (count_exp_nat t1 t2).-1

| CountExpTExpDiff
  of t1 <> t3 & t1 <> TInv t3
: count_exp_nat_TExp_spec t1 t2 t3 (count_exp_nat t1 t2).

Lemma count_exp_nat_TExpP t1 t2 t3 :
  ~~ is_mul t3 ->
  count_exp_nat_TExp_spec t1 t2 t3 (count_exp_nat t1 (TExp t2 t3)).
Proof.
move => Nm3; rewrite (@count_exp_nat_TExp t1 t2 t3 Nm3).
case: (t1 =P TInv t3) => eV; first by constructor.
case: (t1 =P t3) => e; last by constructor.
case: (boolP (_ \in _)) => t1_t2.
- rewrite /count_exp_nat; suff /count_memPn -> : t1 \notin exps t2.
    constructor => //; by rewrite -e.
  by exact: (@in_TInv_expsV t1 t2 t1_t2).
- by constructor => //; rewrite -e.
Qed.

Lemma tsize_TExp_TInv t1 t2 :
  ~~ is_mul (TInv t2) -> t2 \in exps t1 ->
  tsize t2 < tsize t1 /\
  tsize (TInv t2) < tsize t1 /\
  tsize (TExp t1 (TInv t2)) < tsize t1.
Proof.
move => NmI2 H.
have Nm2 : ~~ is_mul t2 := @exps_Nmul t2 t1 H.
rewrite -{1 2 4}(@TExpK' t1 t2 NmI2 Nm2).
set t1' := TExp t1 _; have {}H : TInv t2 \notin exps t1'.
  rewrite -count_exp_nat_gt0 (@count_exp_nat_TExp (TInv t2) t1 (TInv t2) NmI2) -leqNgt.
  rewrite TInvK H count_exp_nat_eq0; last exact: in_TInv_exps.
  by do !case: ifP.
by case: (@tsize_lt_TExp t1' t2 Nm2 H) => ? [] ??; eauto.
Qed.

Lemma exps_sorted t : sorted <=%O (exps t).
Proof.
move: (PreTerm.exps_sorted (wf_unfold_term t)); rewrite -unfold_exps sorted_map.
by [].
Qed.

Lemma exps_Nnil t : is_exp t -> exps t != [::].
Proof.
move => xt.
rewrite -(@is_exp_TExpN (base t) (exps t)
  (is_exp_base t) (atom_exps t) (invs_canceled_exps t)) base_expsK.
exact: xt.
Qed.

Lemma term_lt_rect (T : term -> Type) :
  (forall t, (forall t', (tsize t' < tsize t)%coq_nat -> T t') -> T t) ->
  forall t, T t.
Proof.
move=> H t.
move: {-1}(tsize t) (Nat.le_refl (tsize t)) => n.
elim: n / (lt_wf n) t => n _ IH t t_n.
apply: H => t' t'_t.
apply: (IH (tsize t')); lia.
Qed.

Lemma tsize_in_sumn t' ts : t' \in ts -> tsize t' <= sumn (map tsize ts).
Proof.
elim: ts => // t ts IH; rewrite inE => /orP [/eqP -> /=|/IH h /=].
- exact: leq_addr.
- by rewrite (leq_trans h) // leq_addl.
Qed.

Lemma tsize_base_lt t : is_exp t -> tsize (base t) < tsize t.
Proof.
rewrite is_exp_unfold => xt.
rewrite /tsize unfold_base; move: xt.
by case: (unfold_term t) => [o|o t'|[||] t1 t2|ts] //= _; rewrite ltnS leq_addr.
Qed.

Lemma tsize_exps_lt t' t : t' \in exps t -> tsize t' < tsize t.
Proof.
move => t'_t.
have en : exps t != [::] by apply/eqP => e; rewrite e in_nil in t'_t.
have xt : is_exp t by apply: contraTT en => /exps_expN ->.
rewrite -{1}(base_expsK t)
  (@tsize_TExpN (base t) (exps t) (is_exp_base t) (atom_exps t) (invs_canceled_exps t)).
have /ssrnat.leP := @tsize_in_sumn t' (exps t) t'_t.
have /ssrnat.ltP := tsize_gt0 (base t).
rewrite en /= => ??; apply/ssrnat.ltP; rewrite !addnE; lia.
Qed.

Lemma tfactorsK t : TMulN (tfactors t) = t.
Proof.
apply: unfold_term_inj; rewrite unfold_TMulN unfold_tfactors.
exact: (PreTerm.mul_factors (wf_unfold_term t)).
Qed.

Lemma mul_wf_list_eq ts :
  wf_mul_list ts ->
  PreTerm.mul (map unfold_term ts) = PreTerm.PTMul (map unfold_term ts).
Proof.
move => wf.
have E := PreTerm.normalize_wf (wf_mul_list_unfold ts wf).
move: E => /= <-.
congr PreTerm.mul.
rewrite -map_comp; apply/eq_in_map => t' t'_ts /=; apply/esym.
apply: PreTerm.normalize_wf.
move/allP: (wf_unfold_terms ts); apply; exact: map_f.
Qed.

Lemma is_mul_TMulN ts : wf_mul_list ts -> is_mul (TMulN ts).
Proof. by move => wf; rewrite is_mul_unfold unfold_TMulN mul_wf_list_eq. Qed.

Lemma tfactors_TMulN ts : wf_mul_list ts -> tfactors (TMulN ts) = ts.
Proof.
move => wf; rewrite /tfactors unfold_TMulN mul_wf_list_eq //=.
rewrite -map_comp map_id_in // => t' t'_ts.
exact: unfold_termK.
Qed.

Lemma atom_tfactors t : all (fun t => ~~ is_mul t) (tfactors t).
Proof.
apply/allP => x x_t; rewrite is_mul_unfold.
move: (PreTerm.Nmul_factors (wf_unfold_term t)) => /allP; apply.
by rewrite -unfold_tfactors (map_f _ x_t).
Qed.

Lemma invs_canceled_tfactors t : invs_canceled (tfactors t).
Proof.
rewrite /invs_canceled unfold_tfactors.
exact: PreTerm.invs_canceled_factors (wf_unfold_term t).
Qed.

Lemma tsize_TMulN ts :
  all (fun t => ~~ is_mul t) ts -> invs_canceled ts -> ts != [::] ->
  tsize (TMulN ts) = (1 < size ts) + sumn (map tsize ts).
Proof.
move => atom canc tsN0.
have atomU : all (fun pt => ~~ PreTerm.is_mul pt) (map unfold_term ts).
  rewrite all_map; apply/allP => t' t'ts /=; rewrite -is_mul_unfold.
  by move/allP: atom; apply.
rewrite /tsize /TMulN unfold_TMulN.
rewrite (PreTerm.tsize_mul atomU canc); last by rewrite -size_eq0 size_map size_eq0.
rewrite size_map; congr addn; by rewrite -map_comp.
Qed.

Lemma tsize_tfactors_lt t' t : is_mul t -> t' \in tfactors t -> tsize t' < tsize t.
Proof.
move => xt t'_t.
have tsN0 : tfactors t != [::] by apply/eqP => e; rewrite e in_nil in t'_t.
rewrite -{1}(tfactorsK t)
  (@tsize_TMulN (tfactors t) (atom_tfactors t) (invs_canceled_tfactors t) tsN0).
have /ssrnat.leP := @tsize_in_sumn t' (tfactors t) t'_t.
have szge : 1 < size (tfactors t).
  have szN1 : size (tfactors t) != 1.
    rewrite /tfactors size_map; move: xt; rewrite is_mul_unfold.
    case: (unfold_term t) (wf_unfold_term t) => //= ts /and5P [_ _ _ _] ? _.
    by rewrite /PreTerm.factors.
  by move: szN1 tsN0; case: (tfactors t) => [|?[|??]].
rewrite szge /= => ?; apply/ssrnat.ltP; rewrite !addnE; lia.
Qed.

Lemma term_rect (T : term -> Type)
  (H1 : forall n, T (TInt n))
  (H2 : forall t1, T t1 ->
        forall t2, T t2 ->
        T (TPair t1 t2))
  (H3 : forall a, T (TNonce a))
  (H4 : forall kt t, T t -> T (TKey kt t))
  (H5 : forall k, T k -> forall t, T t -> T (TSeal k t))
  (H6 : forall t, T t -> T (THash t))
  (H7 : forall t, T t -> ~~ is_mul t -> ~~ is_inv t -> T (TInv t))
  (H8 : forall t, T t -> ~~ is_exp t ->
        forall ts, foldr (fun t R => T t * R)%type unit ts ->
                   all (fun t => ~~ is_mul t) ts ->
                   ts != [::] ->
                   sorted <=%O ts ->
                   invs_canceled ts ->
        T (TExpN t ts))
  (H9 : forall ts, foldr (fun t R => T t * R)%type unit ts ->
                   all (fun t => ~~ is_mul t) ts ->
                   sorted <=%O ts ->
                   invs_canceled ts ->
                   size ts != 1 ->
        T (TMulN ts)) :
  forall t, T t.
Proof.
elim/term_lt_rect => t IH.
have build : forall s, (forall t', t' \in s -> tsize t' < tsize t) ->
    foldr (fun t R => T t * R)%type unit s.
  elim => // x s' IHs h; split.
    by apply: IH; apply/ssrnat.ltP; apply: h; rewrite inE eqxx.
  by apply: IHs => t' t's; apply: h; rewrite inE t's orbT.
case: t IH build => [n|t1 t2|a|kt t|k t|t|pt wf nf] IH build.
- exact: H1.
- apply: H2; apply: IH; apply/ssrnat.ltP;
    rewrite [tsize (TPair t1 t2)]tsize_eq ltnS; [exact: leq_addr | exact: leq_addl].
- exact: H3.
- apply: H4; apply: IH; apply/ssrnat.ltP.
  by rewrite [tsize (TKey kt t)]tsize_eq.
- apply: H5; apply: IH; apply/ssrnat.ltP;
    rewrite [tsize (TSeal k t)]tsize_eq ltnS; [exact: leq_addr | exact: leq_addl].
- apply: H6; apply: IH; apply/ssrnat.ltP.
  by rewrite [tsize (THash t)]tsize_eq.
- (* TNonFree pt wf nf — re-split on the head of [pt] *)
  case: pt wf nf IH build => [o|[kt||] operand|[||] b e|ts] wf nf IH build.
  1,2,3,5,6: by move: {IH build} nf; rewrite /is_non_free /=.
  + (* PT1 O1Inv operand: an inverse *)
    have /and3P [Ninvpt Nmpt wfpt] := wf.
    have e : TNonFree (PreTerm.PT1 O1Inv operand) wf nf = TInv (fold_term operand).
      apply: unfold_term_inj.
      by rewrite unfold_TInv (@fold_termK operand wfpt) (@PreTerm.inv_Nmul operand Nmpt)
         (@PreTerm.inv_invN operand Ninvpt).
    have Ninv : ~~ is_inv (fold_term operand) by rewrite is_inv_unfold (@fold_termK operand wfpt).
    have Nmf : ~~ is_mul (fold_term operand) by rewrite is_mul_unfold (@fold_termK operand wfpt).
    rewrite e; apply: (H7 _ _ Nmf Ninv).
    apply: IH.
    rewrite (tsize_eq (TNonFree (PreTerm.PT1 O1Inv operand) wf nf))
            /tsize (@fold_termK operand wfpt) /=.
    apply/ssrnat.ltP; exact: ltnSn.
  + (* PT2 O2Exp b e: an exp *)
    set t := TNonFree (PreTerm.PTExp b e) wf nf.
    have xt : is_exp t by [].
    rewrite -(base_expsK t).
    apply: H8.
    * apply: IH; apply/ssrnat.ltP; exact: tsize_base_lt.
    * exact: is_exp_base.
    * by apply: build => t' t'_t; exact: (@tsize_exps_lt t' t t'_t).
    * exact: atom_exps.
    * exact: exps_Nnil xt.
    * exact: exps_sorted.
    * exact: invs_canceled_exps.
  + (* PTMul ts: a product *)
    set t := TNonFree (PreTerm.PTMul ts) wf nf.
    have xt : is_mul t by [].
    rewrite -(tfactorsK t).
    apply: H9.
    * by apply: build => t' t'_t; exact: (@tsize_tfactors_lt t' t xt t'_t).
    * exact: atom_tfactors.
    * move: (PreTerm.sorted_factors (wf_unfold_term t)); rewrite -unfold_tfactors sorted_map.
      by [].
    * exact: invs_canceled_tfactors.
    * rewrite /tfactors size_map /t /=.
      by have /and5P [_ _ _ _ szN1] := wf.
Qed.

Definition term_ind (P : term -> Prop) := @term_rect P.

Lemma term_lt_ind (T : term -> Prop) :
  (forall t, (forall t', (tsize t' < tsize t)%coq_nat -> T t') -> T t) ->
  forall t, T t.
Proof. exact: term_lt_rect. Qed.

Variant functionality := AENC | SIGN | SENC.

Definition func_of_key_type kt :=
  match kt with
  | AEnc | ADec => AENC
  | Sign | Verify => SIGN
  | SEnc => SENC
  end.

Definition func_of_term t :=
  match t with
  | TKey kt _ => Some (func_of_key_type kt)
  | _ => None
  end.
