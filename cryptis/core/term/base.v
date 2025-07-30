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
  | TExpN' pt pts _ => PreTerm.PTExp pt pts
  end.

Fixpoint fold_term_def pt :=
  match pt with
  | PreTerm.PT0 (O0Int n) => TInt n
  | PreTerm.PT2 O2Pair pt1 pt2 => TPair (fold_term_def pt1) (fold_term_def pt2)
  | PreTerm.PT0 (O0Nonce l) => TNonce l
  | PreTerm.PT1 (O1Key kt) pt => TKey kt (fold_term_def pt)
  | PreTerm.PT2 O2Seal k pt => TSeal (fold_term_def k) (fold_term_def pt)
  | PreTerm.PT1 O1Hash pt => THash (fold_term_def pt)
  | PreTerm.PTExp pt' pts' =>
    if pts' =P [::] is ReflectF pts'N0 then
      TExpN' _ _ (PreTerm.normalize_exp_wf pt' pts' pts'N0)
    else fold_term_def pt'
  end.

Lemma wf_unfold_term t : PreTerm.wf_term (unfold_term t).
Proof. by elim/term_ind': t=> //= ? -> ? ->. Qed.

Fact fold_term_key : unit. Proof. exact: tt. Qed.
Definition fold_term :=
  locked_with fold_term_key fold_term_def.
Canonical fold_term_unlockable := [unlockable of fold_term].

Lemma unfold_termK : cancel unfold_term fold_term.
Proof.
rewrite [fold_term]unlock.
elim/term_ind' => //=.
- by move=> t1 IH1 t2 IH2; rewrite IH1 IH2.
- by move=> kt t IH; rewrite IH.
- by move=> t1 IH1 t2 IH2; rewrite IH1 IH2.
- by move=> t IH; rewrite IH.
- move=> pt pts wf.
  have /and5P [wf_pt ptNexp wf_pts ptsN0 sorted_pts] := wf.
  case: eqP ptsN0 => // ptsN0 _.
  move: (PreTerm.normalize_exp_wf _ _ _).
  set pt' := PreTerm.normalize _.
  rewrite -[PreTerm.exp _ _]/pt' /pt' PreTerm.normalize_wf //=.
  move=> ?; apply: congr1; exact: bool_irrelevance.
Qed.

Lemma unfold_fold pt : unfold_term (fold_term pt) = PreTerm.normalize pt.
Proof.
rewrite [fold_term]unlock; elim: pt => //=.
- by case.
- by case=> [?|] /= ? ->.
- by case=> [] /= ? -> ? ->.
- move=> pt IHpt pts IHpts.
  case: eqP => [->|/eqP ptsN0] //=.
  rewrite PreTerm.base_expsK // PreTerm.is_exp_exp.
  by case: (pts) ptsN0.
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

Section TExp.

Fact TExpN_key : unit. Proof. exact: tt. Qed.
Definition TExpN :=
  locked_with TExpN_key (
    fun t ts =>
      fold_term (PreTerm.PTExp (unfold_term t) (map unfold_term ts))
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

Lemma unfold_TExpN t ts :
  unfold_term (TExpN t ts)
  = PreTerm.exp (unfold_term t) (map unfold_term ts).
Proof.
by rewrite unlock unfold_fold /= normalize_unfold1 normalize_unfoldn.
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
  | PreTerm.PTExp pt pts => TExpN (fold_term pt) (map fold_term pts)
  end.
Proof.
apply/unfold_term_inj. rewrite [fold_term]unlock.
case: pt => //= pt pts; rewrite ?unfold_TExpN.
case: eqP => [->|/eqP ptsN0] //=.
rewrite -unfold_fold unlock -map_comp PreTerm.base_expsK.
- by under [in LHS]eq_map => ? do rewrite -unfold_fold unlock.
- by rewrite PreTerm.is_exp_exp -size_eq0 size_map size_eq0 ptsN0.
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
case: t => //= ?? /and5P [?? /allP wf_ts ??].
rewrite -map_comp map_id_in // => pt /wf_ts pt_in.
by rewrite /= fold_termK.
Qed.

Lemma TExpN_perm t ts1 ts2 : perm_eq ts1 ts2 -> TExpN t ts1 = TExpN t ts2.
Proof.
move=> perm_ts12; apply: unfold_term_inj; rewrite !unfold_TExpN.
apply: PreTerm.perm_exp; exact: perm_map.
Qed.

Lemma TExpNC t ts1 ts2 : TExpN t (ts1 ++ ts2) = TExpN t (ts2 ++ ts1).
Proof. by apply: TExpN_perm; rewrite perm_catC. Qed.

Lemma base_TExpN t ts : base (TExpN t ts) = base t.
Proof.
apply: unfold_term_inj; rewrite !unfold_base unfold_TExpN.
by case: ts=> [|t' ts] //=.
Qed.

Lemma exps_TExpN t ts : exps (TExpN t ts) = sort <=%O (exps t ++ ts).
Proof.
apply: (inj_map unfold_term_inj).
rewrite unfold_exps -sort_map map_cat unfold_exps unfold_TExpN.
rewrite /PreTerm.exp size_map size_eq0.
case: (altP eqP) => [->|tsN0] //=.
rewrite cats0 sort_le_id //.
by case: (unfold_term t) (wf_unfold_term t) => //= ?? /and5P [].
Qed.

Definition is_nonce t :=
  if t is TNonce _ then true else false.

Definition is_exp t :=
  if t is TExpN' _ _ _ then true else false.

Lemma is_nonce_unfold t : is_nonce t = PreTerm.is_nonce (unfold_term t).
Proof. by case: t => //=. Qed.

Lemma is_nonce_TExpN t ts : is_nonce (TExpN t ts) = nilp ts && is_nonce t.
Proof. by rewrite !is_nonce_unfold unfold_TExpN; case: ts. Qed.

Lemma is_nonce_TExp t1 t2 : is_nonce (TExp t1 t2) = false.
Proof. by rewrite is_nonce_TExpN. Qed.

Lemma is_exp_unfold t : is_exp t = PreTerm.is_exp (unfold_term t).
Proof. by case: t => //= - []. Qed.

Lemma is_exp_base t : ~~ is_exp (base t).
Proof.
rewrite is_exp_unfold unfold_base.
case: (unfold_term t) (wf_unfold_term t) => //=.
by move=> ? ? /and5P [].
Qed.

Lemma base_expsK t : TExpN (base t) (exps t) = t.
Proof.
apply/unfold_term_inj; rewrite unfold_TExpN unfold_base unfold_exps.
case: (unfold_term t) (wf_unfold_term t) => //=.
move=> pt pts /and5P [_ ptNexp _ ptsN0 sorted_pts].
rewrite /PreTerm.exp size_eq0 (negbTE ptsN0).
rewrite PreTerm.base_expN // PreTerm.exps_expN //=.
by rewrite sort_le_id.
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

Lemma TExpNA t ts1 ts2 : TExpN (TExpN t ts1) ts2 = TExpN t (ts1 ++ ts2).
Proof.
apply: base_exps_inj; rewrite ?base_TExpN // !exps_TExpN.
rewrite !perm_sort perm_sym perm_sort catA perm_cat2r.
by rewrite perm_sym perm_sort.
Qed.

Lemma is_exp_TExpN t ts : is_exp (TExpN t ts) = (ts != [::]) || is_exp t.
Proof. by rewrite !is_exp_unfold unfold_TExpN; case: ts. Qed.

Lemma is_exp_TExp t1 t2 : is_exp (TExp t1 t2).
Proof. by rewrite is_exp_TExpN. Qed.

Lemma TExpN0 t : TExpN t [::] = t.
Proof.
apply: base_exps_inj; rewrite ?base_TExpN //.
by rewrite exps_TExpN cats0 perm_sort.
Qed.

Definition tsize t := PreTerm.tsize (unfold_term t).

Lemma tsize_gt0 t : 0 < tsize t. Proof. exact: PreTerm.tsize_gt0. Qed.

Lemma tsize_TExpN t ts :
  tsize (TExpN t ts)
  = (ts != [::]) && ~~ is_exp t + tsize t + sumn (map tsize ts).
Proof.
rewrite /tsize unfold_TExpN PreTerm.tsize_exp is_exp_unfold.
rewrite -size_eq0 size_map size_eq0.
case: (altP eqP) => [->|tsN0] //=; rewrite ?addn0 //.
rewrite big_cons big_cat /= sumnE !big_map.
case: (boolP (PreTerm.is_exp (unfold_term t))) => [|tNexp] /=.
- case: t => //= pt pts _ _.
  by rewrite big_cons !big_map !addnA add0n addSn.
- by rewrite PreTerm.base_expN // PreTerm.exps_expN //= big_nil add0n.
Qed.

Lemma TExpN_injl : left_injective TExpN.
Proof.
move=> ts t1 t2 e; apply: base_exps_inj.
- by move/(congr1 base): e; rewrite !base_TExpN.
- move/(congr1 exps): e; rewrite !exps_TExpN.
  by move/perm_sort_leP; rewrite perm_cat2r.
Qed.

Lemma TExpN_injr t ts1 ts2 : TExpN t ts1 = TExpN t ts2 -> perm_eq ts1 ts2.
Proof.
move=> /(congr1 exps); rewrite !exps_TExpN; move/perm_sort_leP.
by rewrite perm_cat2l.
Qed.

Lemma TExp_injr t t1 t2 : TExp t t1 = TExp t t2 -> t1 = t2.
Proof.
by move/TExpN_injr/perm_mem/(_ t2); rewrite !inE eqxx => /eqP.
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
  end.
Proof. by case: t. Qed.

Lemma tsize_TExpN_lt t1 ts1 t2 :
  (tsize (TExpN t1 ts1) < tsize (TExpN t1 (t2 :: ts1)))%coq_nat /\
  (tsize t2 < tsize (TExpN t1 (t2 :: ts1)))%coq_nat.
Proof.
move/ssrnat.ltP: (tsize_gt0 t1) => pos_t1.
move/ssrnat.ltP: (tsize_gt0 t2) => pos_t2.
rewrite !tsize_TExpN /= -!plusE; case: (altP eqP) => [->|ts1N0] //=; lia.
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
  (H7 : forall t, T t -> ~~ is_exp t ->
        forall ts, foldr (fun t R => T t * R)%type unit ts ->
                   ts != [::] ->
                   sorted <=%O ts ->
        T (TExpN t ts)) :
  forall t, T t.
Proof.
move=> t; rewrite -(unfold_termK t) [fold_term]unlock.
move: (wf_unfold_term t).
elim: (unfold_term t) => {t} /=.
- by case=> *; eauto.
- by case=> *; eauto.
- by case=> [] t1 IH1 t2 IH2 /andP [/IH1 ? /IH2 ?]; eauto.
move=> pt IHpt pts IHpts /and5P [wf_pt ptNexp wf_pts ptsN0 sorted_pts].
case: eqP ptsN0 => //= ptsN0 _.
have [t e_pt] : {t | pt = unfold_term t}.
  by exists (fold_term pt); rewrite fold_termK.
rewrite {}e_pt {pt} in IHpt wf_pt ptNexp *.
have [ts e_pts] : {ts | pts = map unfold_term ts}.
  exists (map fold_term pts).
  rewrite -map_comp map_id_in // => pt' pt'_pts.
  by rewrite /= fold_termK // (allP wf_pts).
move: (PreTerm.normalize_exp_wf _ _ _) => wf.
have tsN0: ts != [::].
  by move/eqP: ptsN0; rewrite e_pts -!size_eq0 size_map.
rewrite {}e_pts {pts ptsN0} in IHpts wf_pts sorted_pts wf *.
rewrite (_ : TExpN' _ _ _ = TExpN t ts); last first.
  apply: unfold_term_inj.
  rewrite unfold_TExpN /PreTerm.exp /= !size_map size_eq0 (negbTE tsN0).
  by rewrite normalize_unfold1 normalize_unfoldn.
apply: H7 => //.
- by rewrite -(unfold_termK t) unlock; apply: IHpt.
- by rewrite is_exp_unfold.
- elim: ts IHpts wf_pts {wf tsN0 sorted_pts} => /= [[] //|t' ts IH [] IHt /IH IHts].
  case/andP => {}/IHt IHt {}/IHts IHts; split => //.
  by rewrite -[t']unfold_termK unlock.
- by move: sorted_pts; rewrite sorted_map.
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
