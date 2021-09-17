From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From iris.proofmode Require Import base environments.
From cryptis Require Import lib term cryptis primitives.
Import bi.
Import env_notations.

Section Proofs.

Context `{!heapGS Σ, !cryptisG Σ}.

Implicit Types E : coPset.
Implicit Types l : loc.
Implicit Types t : term.
Implicit Types v : val.
Implicit Types Φ : prodO locO termO -n> iPropO Σ.
Implicit Types Ψ : val → iProp Σ.

Lemma tac_wp_cons `{!Repr A} Γ E K (x : A) (xs : list A) Ψ :
  envs_entails Γ (WP fill K (Val (repr (x :: xs)%list)) @ E {{ Ψ }}) →
  envs_entails Γ (WP fill K (repr x :: repr xs) : expr @ E {{ Ψ }}).
Proof.
rewrite envs_entails_eq => post.
by rewrite -wp_bind -wp_cons.
Qed.

Lemma tac_wp_cons1 `{!Repr A} Γ E K (x : A) Ψ :
  envs_entails Γ (WP fill K (Val (repr [x]%list)) @ E {{ Ψ }}) →
  envs_entails Γ (WP fill K (repr x :: []%V) @ E {{ Ψ }}).
Proof.
rewrite (_ : NILV = repr (@nil A)) /=; first by apply: tac_wp_cons.
by rewrite repr_list_eq /=.
Qed.

Lemma tac_wp_list_match `{!Repr A} Γ E K vars vs k Ψ :
  nforall_eq (length vars) vs (
    λ vs', envs_entails Γ (WP fill K (nsubst vars (map repr vs') k) @ E {{ Ψ }})) →
  (length vars ≠ length vs →
    envs_entails Γ (WP fill K NONEV @ E {{ Ψ }})) →
  envs_entails Γ (WP fill K (list_match vars (repr vs) k) @ E {{ Ψ }}).
Proof.
rewrite envs_entails_eq => /nforallP hyes hno.
rewrite -wp_bind -wp_list_match.
case: decide => [e_len|ne_len]; last by iApply hno.
by rewrite -wp_bind_inv; iApply hyes.
Qed.

Lemma tac_wp_hash Γ E K t Ψ :
  envs_entails Γ (WP fill K (Val (THash t)) @ E {{ Ψ }}) →
  envs_entails Γ (WP fill K (hash t) @ E {{ Ψ }}).
Proof.
rewrite envs_entails_eq => post.
by rewrite -wp_bind -wp_hash.
Qed.

Lemma tac_wp_tag Γ E K N t Ψ :
  envs_entails Γ (WP fill K (Val (Spec.tag N t)) @ E {{ Ψ }}) →
  envs_entails Γ (WP fill K (tag N t) @ E {{ Ψ }}).
Proof.
rewrite envs_entails_eq => ?.
by rewrite -wp_bind -wp_tag.
Qed.

Lemma tac_twp_untag Γ E K n t Ψ :
  (∀ t', t = Spec.tag n t' →
         envs_entails Γ (WP fill K (Val (repr (Some t'))) @ E [{ Ψ }])) →
  (Spec.untag n t = None →
   envs_entails Γ (WP fill K (Val NONEV) @ E [{ Ψ }])) →
  envs_entails Γ (WP fill K (untag n t) @ E [{ Ψ }]).
Proof.
rewrite envs_entails_eq => HSome HNone.
rewrite -twp_bind -twp_untag.
case e: Spec.untag => [t'|].
- by move/Spec.untagK in e; apply: HSome.
- exact: HNone.
Qed.

Lemma tac_wp_untag Γ E K n t Ψ :
  (∀ t', t = Spec.tag n t' →
         envs_entails Γ (WP fill K (Val (repr (Some t'))) @ E {{ Ψ }})) →
  (Spec.untag n t = None →
   envs_entails Γ (WP fill K (Val NONEV) @ E {{ Ψ }})) →
  envs_entails Γ (WP fill K (untag n t) @ E {{ Ψ }}).
Proof.
rewrite envs_entails_eq => HSome HNone.
rewrite -wp_bind -wp_untag.
case e: Spec.untag => [t'|].
- by move/Spec.untagK in e; apply: HSome.
- exact: HNone.
Qed.

Lemma tac_twp_dec Γ E K k t Ψ :
  (∀ t', t = TEnc k t' →
         envs_entails Γ (WP fill K (Val (SOMEV t')) @ E [{ Ψ }])) →
  (Spec.dec (TKey Dec k) t = None →
   envs_entails Γ (WP fill K (Val NONEV) @ E [{ Ψ }])) →
  envs_entails Γ (WP fill K (dec (TKey Dec k) t) @ E [{ Ψ }]).
Proof.
rewrite envs_entails_eq => HSome HNone.
rewrite -twp_bind -twp_dec.
case: t HSome HNone; eauto => k' /=.
by case: decide => [<-|]; eauto.
Qed.

Lemma tac_wp_dec Γ E K k t Ψ :
  (∀ t', t = TEnc k t' →
         envs_entails Γ (WP fill K (Val (SOMEV t')) @ E {{ Ψ }})) →
  (Spec.dec (TKey Dec k) t = None →
   envs_entails Γ (WP fill K (Val NONEV) @ E {{ Ψ }})) →
  envs_entails Γ (WP fill K (dec (TKey Dec k) t) @ E {{ Ψ }}).
Proof.
rewrite envs_entails_eq => HSome HNone.
rewrite -wp_bind -wp_dec.
case: t HSome HNone; eauto => k' /=.
by case: decide => [<-|]; eauto.
Qed.

Lemma tac_wp_tenc Γ E K c t1 t2 Ψ :
  envs_entails Γ (WP fill K (Val (Spec.tenc c t1 t2)) @ E {{ Ψ }}) →
  envs_entails Γ (WP fill K (tenc c t1 t2) @ E {{ Ψ }}).
Proof.
rewrite envs_entails_eq => H.
by rewrite -wp_bind -wp_tenc.
Qed.

(* MOVE *)
Lemma tdecK c k t t' :
  Spec.tdec c (TKey Dec k) t = Some t' →
  t = TEnc k (Spec.tag c t').
Proof.
rewrite /Spec.tdec /=.
case: t => [] //= k' t.
by case: decide => //= <- /Spec.untagK ->.
Qed.
(* /MOVE *)

Lemma tac_wp_tdec Γ E K c k t Ψ :
  (∀ t', t = TEnc k (Spec.tag c t') →
         envs_entails Γ (WP fill K (Val (SOMEV t')) @ E {{ Ψ }})) →
  (Spec.tdec c (TKey Dec k) t = None →
   envs_entails Γ (WP fill K (Val NONEV) @ E {{ Ψ }})) →
  envs_entails Γ (WP fill K (tdec c (TKey Dec k) t) @ E {{ Ψ }}).
Proof.
rewrite envs_entails_eq => HSome HNone.
rewrite -wp_bind -wp_tdec.
case e: Spec.tdec => [t'|]; eauto.
by apply: HSome; apply: tdecK.
Qed.

Lemma tac_wp_list Γ E K (ts : list term) Ψ :
  envs_entails Γ (WP fill K (Val (repr ts)) @ E {{ Ψ }}) →
  envs_entails Γ (WP fill K (list_to_expr ts) @ E {{ Ψ }}).
Proof.
rewrite envs_entails_eq => post.
by rewrite -wp_bind -wp_list.
Qed.

Lemma tac_twp_list_of_term Γ E K t Ψ :
  (∀ ts, t = Spec.of_list ts →
         envs_entails Γ (WP fill K (Val (SOMEV (repr ts))) @ E [{ Ψ }])) →
  (Spec.to_list t = None →
   envs_entails Γ (WP fill K NONEV @ E [{ Ψ }])) →
  envs_entails Γ (WP fill K (list_of_term t) @ E [{ Ψ }]).
Proof.
rewrite envs_entails_eq => HSome HNone.
rewrite -twp_bind -twp_list_of_term.
case e: Spec.to_list => [ts|]; eauto.
move/Spec.to_listK in e; subst t; eauto.
Qed.

Lemma tac_wp_list_of_term Γ E K t Ψ :
  (∀ ts, t = Spec.of_list ts →
         envs_entails Γ (WP fill K (Val (SOMEV (repr ts))) @ E {{ Ψ }})) →
  (Spec.to_list t = None →
   envs_entails Γ (WP fill K NONEV @ E {{ Ψ }})) →
  envs_entails Γ (WP fill K (list_of_term t) @ E {{ Ψ }}).
Proof.
rewrite envs_entails_eq => HSome HNone.
rewrite -wp_bind -wp_list_of_term.
case e: Spec.to_list => [ts|]; eauto.
move/Spec.to_listK in e; subst t; eauto.
Qed.

(* TODO:
- Generalize to other instances of Repr
- rename get_list -> lookup *)
Lemma tac_twp_lookup Γ E K ts (n : Z) Ψ :
  (0 <= n)%Z →
  (∀ t, (ts !! Z.to_nat n)%stdpp = Some t →
        envs_entails Γ (WP fill K (Val (SOMEV t)) @ E [{ Ψ }])) →
  ((ts !! Z.to_nat n)%stdpp = None →
   envs_entails Γ (WP fill K (Val NONEV) @ E [{ Ψ }])) →
  envs_entails Γ (WP fill K (repr ts !! #n)%E @ E [{ Ψ }]).
Proof.
move=> npos; rewrite -[in #n](Z2Nat.id n) //.
move: (Z.to_nat _)=> {npos} n.
rewrite envs_entails_eq => HSome HNone.
rewrite -twp_bind -twp_get_list.
by case e: (_ !! n)%stdpp => [t|]; eauto.
Qed.

Lemma tac_wp_lookup Γ E K ts (n : Z) Ψ :
  (0 <= n)%Z →
  (∀ t, (ts !! Z.to_nat n)%stdpp = Some t →
        envs_entails Γ (WP fill K (Val (SOMEV t)) @ E {{ Ψ }})) →
  ((ts !! Z.to_nat n)%stdpp = None →
   envs_entails Γ (WP fill K (Val NONEV) @ E {{ Ψ }})) →
  envs_entails Γ (WP fill K (repr ts !! #n)%E @ E {{ Ψ }}).
Proof.
move=> npos; rewrite -[in #n](Z2Nat.id n) //.
move: (Z.to_nat _)=> {npos} n.
rewrite envs_entails_eq => HSome HNone.
rewrite -wp_bind -wp_get_list.
by case e: (_ !! n)%stdpp => [t|]; eauto.
Qed.

Lemma tac_wp_eq_term Γ E K t1 t2 Ψ :
  (t1 = t2 →
   envs_entails Γ (WP fill K (Val #true) @ E {{ Ψ }})) →
  (t1 ≠ t2 →
   envs_entails Γ (WP fill K (Val #false) @ E {{ Ψ }})) →
  envs_entails Γ (WP fill K (eq_term t1 t2) @ E {{ Ψ }}).
Proof.
rewrite envs_entails_eq => HSome HNone.
rewrite -wp_bind -wp_eq_term.
by case: bool_decide_reflect; eauto.
Qed.

Lemma tac_wp_is_key Γ E K t Ψ :
  (∀ kt k, t = TKey kt k →
           envs_entails Γ (WP fill K (Val (SOMEV (repr kt))) @ E {{ Ψ }})) →
  (Spec.is_key t = None →
   envs_entails Γ (WP fill K (Val NONEV) @ E {{ Ψ }})) →
  envs_entails Γ (WP fill K (is_key t) @ E {{ Ψ }}).
Proof.
rewrite envs_entails_eq => HSome HNone.
rewrite -wp_bind -wp_is_key.
case: t HSome HNone; eauto.
by move=> kt k HSome _ /=; eapply HSome.
Qed.

End Proofs.

Tactic Notation "wp_cons" :=
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    reshape_expr e ltac:(fun K e' =>
      lazymatch e' with
      | App (App (Val CONS) (Val (?f ?x))) (Val ?e'') =>
        lazymatch e'' with
        | InjLV (LitV LitUnit) =>
          let A := type of x in
          first
            [eapply (@tac_wp_cons1 _ _ A _ _ _ K x _); wp_finish
            |fail 1 "wp_cons: Cannot decode"]
        | _ =>
          first
            [eapply (tac_wp_cons _ _ K x _ _); wp_finish
            |fail 1 "wp_cons: Cannot decode"]
        end
      end)
  end.

Tactic Notation "wp_list" := repeat wp_cons.

Tactic Notation "wp_list_match" :=
  wp_pures;
  do ?[rewrite subst_list_match /=];
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    reshape_expr e ltac:(fun K e' =>
      lazymatch e' with
      | list_match ?vars (Val (?f ?xs)) ?k =>
        lazymatch type of xs with
        | list ?A =>
          first
            [eapply (@tac_wp_list_match _ _ A _ _ E K vars xs k); simpl
            |fail 1 "wp_list_match: Cannot decode"]
        end
      end)
  end.

Tactic Notation "wp_term_of_list" :=
  wp_pures; try wp_bind (term_of_list _); iApply wp_term_of_list.

Tactic Notation "wp_enc" :=
  wp_pures; try wp_bind (enc _ _); iApply wp_enc.

Tactic Notation "wp_tenc" :=
  wp_pures; try wp_bind (tenc _ _ _); iApply wp_tenc.

Tactic Notation "wp_hash" :=
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    reshape_expr e ltac:(fun K e' =>
      first
        [eapply (tac_wp_hash _ _ K _ _); wp_finish
        |fail 1 "wp_hash: Cannot decode"])
  end.

Tactic Notation "wp_dec_eq" ident(t) ident(H) :=
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    reshape_expr e ltac:(fun K e' =>
      first
        [eapply (tac_wp_dec _ _ K _ _);
         [intros t H|intros H];
         wp_finish
        |fail 1 "wp_dec: Cannot decode"])
  end.

Tactic Notation "wp_dec" ident(t) :=
  let tf := fresh "tf" in
  let H := fresh "H" in
  wp_dec_eq tf H; [
    first [revert t tf H; intros _ t ->
          |revert tf H; intros _ t ->
          |revert tf H; intros t _]
  | clear H].

Tactic Notation "wp_tdec_eq" ident(t) ident(H) :=
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    reshape_expr e ltac:(fun K e' =>
      first
        [eapply (tac_wp_tdec _ _ K _ _);
         [intros t H|intros H];
         wp_finish
        |fail 1 "wp_tdec: Cannot decode"])
  end.

Tactic Notation "wp_tdec" ident(t) :=
  let tf := fresh "tf" in
  let H := fresh "H" in
  wp_tdec_eq tf H; [
    first [revert t tf H; intros _ t ->
          |revert tf H; intros _ t ->
          |revert tf H; intros t _]
  | clear H].

Tactic Notation "wp_list_of_term_eq" ident(t) ident(H) :=
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    reshape_expr e ltac:(fun K e' =>
      first
        [eapply (tac_wp_list_of_term _ _ K _ _);
         [intros t H|intros H];
         wp_finish
        |fail 1 "wp_dec: Cannot decode"])
  end.

Tactic Notation "wp_list_of_term" ident(t) :=
  let tf := fresh "tf" in
  let H := fresh "H" in
  wp_list_of_term_eq tf H; [
    first [revert t tf H; intros _ t ->
          |revert tf H; intros _ t ->
          |revert tf H; intros t _]
  | clear H].

Tactic Notation "wp_lookup" ident(t) ident(H) :=
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    reshape_expr e ltac:(fun K e' =>
      first
        [eapply (tac_wp_lookup _ _ K _ _);
         [lia|intros t H|intros H];
         wp_finish
        |fail 1 "wp_lookup: Cannot decode"])
  end.

Tactic Notation "wp_eq_term" ident(H) :=
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    reshape_expr e ltac:(fun K e' =>
      first
        [eapply (tac_wp_eq_term _ _ K _ _); intros H; wp_finish
        |fail 1 "wp_eq_term: Cannot decode"])
  end.

Tactic Notation "wp_tag" :=
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    reshape_expr e ltac:(fun K e' =>
      first
        [eapply (tac_wp_tag _ _ K _ _); wp_finish
        |fail 1 "wp_tag: Cannot decode"])
  end.

Tactic Notation "wp_untag_eq" ident(t) ident(H) :=
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    reshape_expr e ltac:(fun K e' =>
      first
        [eapply (tac_wp_untag _ _ K _ _);
         [intros t H|intros H];
         wp_finish
        |fail 1 "wp_untag_eq: Cannot decode"])
  end.

Tactic Notation "wp_untag" ident(t) :=
  let tf := fresh "tf" in
  let H := fresh "H" in
  wp_untag_eq tf H; [
    first [revert t tf H; intros _ t ->
          |revert tf H; intros _ t ->
          |revert tf H; intros t _]
  | clear H].

Tactic Notation "wp_is_key_eq" ident(kt) ident(k) ident(H) :=
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    reshape_expr e ltac:(fun K e' =>
      first
        [eapply (tac_wp_is_key _ _ K _ _);
         [intros kt k H|intros H];
         wp_finish
        |fail 1 "wp_untag_eq: Cannot decode"])
  end.
