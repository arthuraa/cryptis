From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From iris.proofmode Require Import base environments.
From crypto Require Import lib basic term crypto1 primitives.
Import bi.
Import env_notations.

Section Proofs.

Context `{!heapG Σ, !resG Σ}.

Implicit Types E : coPset.
Implicit Types l : loc.
Implicit Types lvl : level.
Implicit Types t : term.
Implicit Types v : val.
Implicit Types Φ : prodO locO termO -n> iPropO Σ.
Implicit Types Ψ : val → iProp Σ.

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

(* TODO: Generalize to symmetric encryption *)
Lemma tac_twp_dec Γ E K k t Ψ :
  (∀ t', t = TEnc true k t' →
         envs_entails Γ (WP fill K (Val (SOMEV t')) @ E [{ Ψ }])) →
  (Spec.dec (TKey KADec k) t = None →
   envs_entails Γ (WP fill K (Val NONEV) @ E [{ Ψ }])) →
  envs_entails Γ (WP fill K (dec (TKey KADec k) t) @ E [{ Ψ }]).
Proof.
rewrite envs_entails_eq => HSome HNone.
rewrite -twp_bind -twp_dec.
case: t HSome HNone; eauto.
case; eauto => k' /=.
by case: decide => [<-|]; eauto.
Qed.

Lemma tac_wp_dec Γ E K k t Ψ :
  (∀ t', t = TEnc true k t' →
         envs_entails Γ (WP fill K (Val (SOMEV t')) @ E {{ Ψ }})) →
  (Spec.dec (TKey KADec k) t = None →
   envs_entails Γ (WP fill K (Val NONEV) @ E {{ Ψ }})) →
  envs_entails Γ (WP fill K (dec (TKey KADec k) t) @ E {{ Ψ }}).
Proof.
rewrite envs_entails_eq => HSome HNone.
rewrite -wp_bind -wp_dec.
case: t HSome HNone; eauto.
case; eauto => k' /=.
by case: decide => [<-|]; eauto.
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

Tactic Notation "wp_list" open_constr(t) :=
  wp_pures; wp_bind (_ :: _)%E; iApply (wp_list t).

Tactic Notation "wp_term_of_list" :=
  wp_pures; wp_bind (term_of_list _); iApply wp_term_of_list.

Tactic Notation "wp_tag" :=
  wp_pures; wp_bind (tag _ _); iApply wp_tag.

Tactic Notation "wp_enc" :=
  wp_pures; wp_bind (enc _ _); iApply wp_enc.

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
