From cryptis Require Import lib.
From elpi.apps Require Import locker.
From mathcomp Require Import ssreflect.
From Stdlib Require Import ZArith.ZArith Lia.
From stdpp Require Import sorting gmap.
From cryptis.lib Require Import list_sort mathcomp_compat sms.
From iris.heap_lang Require locations.
From iris.heap_lang Require Import notation.
From iris.heap_lang Require Import primitive_laws.
From cryptis.core Require Export pre_term.
From cryptis.core.term Require Import base algebra tsize repr nonces subterms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Implicit Types (t k : term) (ts : list term).

(* Surface API: Tag and Module Spec (tag/untag, of_list/to_list, open, key predicates, enc/dec), plus trailing exponentiation lemmas.
   (Split out of the former monolithic core/term/base.v.) *)

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
rewrite [tsize (TPair _ _)]tsizeE; case=> [<-|/IH t_ts]; lia.
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

Lemma TExp_TExpN t1 ts1 t2 : TExp (TExpN t1 ts1) t2 = TExpN t1 (t2 :: ts1).
Proof.
have -> : TExp (TExpN t1 ts1) t2 = TExpN (TExpN t1 ts1) [t2].
  by rewrite /TExpN TMulN1.
rewrite TExpNA; apply: TExpN_perm.
by rewrite -Permutation_cons_append.
Qed.

Lemma exps_count_TExpNW t1 t2 ts :
  atomic ts ->
  (∀ t, t ∈ ts → t1 ≠ TInv t) →
  (SMS.count TInv t1 (exps t2) ≤ SMS.count TInv t1 (exps (TExpN t2 ts)))%Z.
Proof.
elim: ts => [|t ts IH]; first by move => _ _; rewrite TExpN0; lia.
move => atom t1_ts.
move: atom => /Forall_cons [Nmt atom'].
rewrite -TExp_TExpN; set t2' := TExpN t2 ts.
apply: (Z.le_trans _ (SMS.count TInv t1 (exps t2'))).
- apply: (IH atom') => t' t'_ts; apply: t1_ts; rewrite elem_of_cons; eauto.
- apply: (exps_count_TExpW t1 t2' t Nmt); move/(_ t): t1_ts; apply.
  rewrite elem_of_cons; by eauto.
Qed.

Lemma elem_of_TExpN2l g t1 t2 :
  negb (is_mul t1) -> negb (is_mul t2) ->
  t1 ≠ TInv t2 →
  TInv t1 ∉ exps g →
  t1 ∈ exps (TExpN g [t1; t2]).
Proof.
move=> Nm1 Nm2 t1_t2 t1_g.
rewrite (not_elem_of_TInv_exps _ Nm1) -exps_count_gt0 in t1_g.
have e : TExpN g [t1; t2] = TExp (TExp g t1) t2.
  rewrite (_ : TExp g t1 = TExpN g [t1]); last by rewrite /TExpN TMulN1.
  rewrite TExp_TExpN; exact: TExpC2.
rewrite e -exps_count_gt0 (exps_count_TExp t1 (TExp g t1) t2 Nm2).
rewrite (@decide_False _ (t1 = TInv t2)); last exact: t1_t2.
by case: decide; lia.
Qed.

Lemma elem_of_TExpN2r g t1 t2 :
  negb (is_mul t1) -> negb (is_mul t2) ->
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
Proof. move=> tNX; apply: base_expN_bool; apply/negb_True; exact: tNX. Qed.

Lemma exps_expN t : ¬ is_exp t → exps t = [].
Proof. move=> tNX; apply: exps_expN_bool; apply/negb_True; exact: tNX. Qed.

Lemma exps_TExpN' t ts :
  ¬ is_exp t -> atomic ts ->
  (forall t', t' ∈ ts -> TInv t' ∉ ts) ->
  exps (TExpN t ts) ≡ₚ ts.
Proof.
move => tNexp atom nc.
rewrite (@exps_TExpN t ts atom) (exps_expN tNexp) app_nil_l.
exact: (to_perm_id _ nc).
Qed.

Lemma is_exp_base t : ¬ is_exp (base t).
Proof. apply/negb_True; exact: is_exp_base_bool. Qed.
Hint Resolve is_exp_base : core.

(* Re-export the [Set Implicit Arguments] argument structure that the old
   with_stdpp.v restatements provided for these lemmas, so downstream callers
   that pass only the hypotheses keep working. *)
Arguments tsize_lt_TExp {t1 t2} _ _.
Arguments tsize_TExp_TInv {t1 t2} _ _.
