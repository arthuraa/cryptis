From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.heap_lang Require Import notation proofmode.
From Stdlib Require Import ZArith Lia Field.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis.lib Require Import dh list_sort poly poly_gcd poly_restrict frac.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * HMQV key exchange

    HQMV is an authenticated version of Diffie-Hellman key exchange.  Each party
    [i] holds a pair of long-term keys: a private key [p_i] and a public key
    [P_i = g^p_i], where [g] is a generator of the Diffie-Hellman group.  If [i]
    wants to exchange a key with [j], they proceed as follows:

             X_i, P_i
        i ----------------> j

             X_j, P_j
        i <---------------- j


    where each [X = g^x] is an _ephemeral_ public key generated from a fresh
    private key [x].  Each party can compute the shared key [K], where

        K   = (X_j P_j^m_j) ^ (x_i + m_i · p_i)
            = (X_i P_i^m_i) ^ (x_j + m_j · p_j)

        m_i = H(t_i, X_i, P_j)
        m_j = H(t_j, X_j, P_i),

    and [t_i] and [t_j] are a pair of fixed, distinct tags used to disambiguate
    the multipliers [m_i] and [m_j].  This key can only be computed by knowing the
    long-term and ephemeral private keys belonging to one of the parties, so any
    communication that uses this key is implicitly authenticated.

    This file establishes basic results about the HMQV key exchange formula.
    Exponents form a field, so the key raises [Y_j = X_j P_j^m_j] to the
    scalar [x_i + m_i ⋅ p_i] ([hmqv_s]), and the proofs compare the
    logarithms of keys ([log]) as fractions.


    [hmqv_K t_a t_b p_a x_a P_a X_a P_b X_b] computes the key formula from the
    tags, a party's private keys [p_a] and [x_a], its own public keys [P_a] and
    [X_a] and the peer's public keys [P_b] and [X_b].  The multipliers are
    [hmqv_m t X P = H(t, X, P)].  We prove the following properties:

    - [hmqv_K_sym]: [hmqv_K] produces the same key for the two parties.  This
      property allows them to agree on a shared session key.

    - [hmqv_K_inj']: the session key [K] of an initiator and that of a
      responder determine which long-term and ephemeral keys were used.  The
      long-term keys that the parties accepted for their peers need not be
      vetted, but neither they nor [K] may be the group identity; a vetted
      long-term key is not, and neither is a key computed with it
      ([hmqv_K_neq_unit]).  If the agents' long-term keys represent their
      identity, this means that the key binds who participated in the key
      exchange, an authentication guarantee.

    - [hmqv_K_inj]: two keys of the same role, under the same conditions,
      have the same private keys and the same claimed peer long-term key, but
      not necessarily the same peer ephemeral: a rogue long-term key
      [(X_b ⋅ X_b'⁻¹)^(1/(m_b' - m_b))] makes two peer ephemerals give the
      same key for one ephemeral private key.  Thus, if ephemeral keys are used
      only once, the key determines the session.  [hmqv_K_inj_vetted]: a vetted
      peer long-term key also binds the peer ephemeral.

    - [hmqv_K_unit]: if the session key is the group identity, then so is the
      base [hmqv_Y] that the party exponentiated, whatever (unvetted) peer keys
      it used.

    - [hmqv_K_inj_base]: for a fixed claimed long-term key [P_b], the key
      determines the base [hmqv_Y] the initiator exponentiated, whatever
      (unvetted) peer ephemeral it used.

    - [hmqv_K_inj_counterexample]: excluding a trivial key is not enough to
      bind an unvetted peer: two different peer-key pairs, one of them with
      [P_b = 1], yield the same key [≠ 1].

    - [public_hmqv_K_honest]: a forward secrecy guarantee. A key exchanged by
      two honest parties can only be compromised if one of the parties had both
      long-term and ephemeral secret keys compromised eventually.

    - [public_hmqv_K_forged]: suppose that an honest party [i] attempts to
      authenticate with another party [j], but ends up contacting a dishonest
      party pretending to be [j].  The exchanged session key will only be public
      if either [j]'s long-term secret key was compromised or if [i] had both
      long-term and ephemeral secret keys compromised.  This is a form of
      resistance against key compromise impersonation (KCI) attacks: knowledge
      of [i]'s long-term secret key is not enough for a malicious party to trick
      [i] into believing that they are talking to an honest party [j].

    Whether a private key is secret is up to its owner; the lemmas only assume
    the DH exponent predicate [hmqv_key] and conclude which keys are public.
    [ephemeral x] adds that [x] never leaks, as for an ephemeral private key
    deleted right away.

*)

Section HMQV.

Variable N : namespace.
Variable g : term.

Add Field hmqv_field : (Frac.frac_field_theory (T := term)).

(** The multiplier of a party whose ephemeral public key is [X] and whose peer
    has long-term public key [P]. *)

Definition hmqv_m (t : string) (X P : term) : term :=
  THash (Spec.tag (Tag $ N.@t) (Spec.of_list [X; P])).

#[local] Lemma hmqv_m_inj t t' X X' P P' :
  hmqv_m t X P = hmqv_m t' X' P' → t = t' ∧ X = X' ∧ P = P'.
Proof.
rewrite /hmqv_m => - [] /Spec.tag_inj [] /Tag_inj c /Spec.of_list_inj [] -> ->.
by case: (ndot_inj _ _ _ _ c).
Qed.

#[local] Lemma tsize_hmqv_m_lt t X P : tsize X < tsize (hmqv_m t X P).
Proof.
rewrite /hmqv_m [Spec.tag]unlock.
have e : tsize (THash (TPair (Tag (N.@t)) (Spec.of_list [X; P])))
       = S (S (tsize (Tag (N.@t)) + tsize (Spec.of_list [X; P]))).
  by rewrite [tsize (THash _)]tsize_eq [tsize (TPair _ _)]tsize_eq.
rewrite e.
have X_in : X ∈ [X; P] by set_solver.
have := Spec.of_list_tsize X_in; lia.
Qed.

#[local] Lemma tsize_hmqv_m_lt2 t X P : tsize P < tsize (hmqv_m t X P).
Proof.
rewrite /hmqv_m [Spec.tag]unlock.
have e : tsize (THash (TPair (Tag (N.@t)) (Spec.of_list [X; P])))
       = S (S (tsize (Tag (N.@t)) + tsize (Spec.of_list [X; P]))).
  by rewrite [tsize (THash _)]tsize_eq [tsize (TPair _ _)]tsize_eq.
rewrite e.
have P_in : P ∈ [X; P] by set_solver.
have := Spec.of_list_tsize P_in; lia.
Qed.

#[local] Lemma hmqv_m_Nmod t X P : negb (is_mod (hmqv_m t X P)).
Proof. by rewrite /hmqv_m. Qed.

Definition hmqv_Y (t_b : string) (P_a P_b X_b : term) : term :=
  TGMul {[+ X_b; TExp P_b (hmqv_m t_b X_b P_a) +]}.

(** The scalar [x + m⋅p]. *)
Definition hmqv_s (m p x : term) : term := TSum {[+ x; TMul {[+ m; p +]} +]}.

Definition hmqv_K (t_a t_b : string) (p_a x_a P_a X_a P_b X_b : term) : term :=
  TExp (hmqv_Y t_b P_a P_b X_b) (hmqv_s (hmqv_m t_a X_a P_b) p_a x_a).

(** ** Fractions and atoms *)

#[local] Lemma free_nonce t X P (n : nonce) : hmqv_m t X P ∉ atoms (TNonce n).
Proof. exact: not_elem_of_atoms_atom. Qed.

#[local] Lemma free_hmqv_s t X P m (p x : nonce) :
  hmqv_m t X P ≠ m → negb (is_mod m) → hmqv_m t X P ∉ atoms (hmqv_s m p x).
Proof.
move=> ne nm; apply: not_elem_of_atoms_TSum2; first exact: free_nonce.
by apply: not_elem_of_atoms_TMul2;
  [exact: not_elem_of_atoms_atom|exact: free_nonce].
Qed.

#[local] Lemma frac_hmqv_s m p x :
  frac_of (hmqv_s m p x) =
  Frac.add (frac_of x) (Frac.mul (frac_of m) (frac_of p)).
Proof.
by rewrite /hmqv_s frac_of_TSum Frac.ssum_disj_union !Frac.ssum_singleton
  frac_of_TMul2.
Qed.

#[local] Lemma hmqv_s_neq0 t X P (p x : nonce) :
  frac_of (hmqv_s (hmqv_m t X P) p x) ≠ Frac.zero.
Proof.
set m := hmqv_m t X P; rewrite frac_hmqv_s => e.
have [ex _] : TNonce x = TSum ∅ ∧ TNonce p = TSum ∅.
  apply: (frac_lin (h := m)); try exact: free_nonce; try
    exact: not_elem_of_atoms_TSum_empty.
  - exact: hmqv_m_Nmod.
  - rewrite frac_of_TSum_empty.
    transitivity (Frac.add (frac_of (TNonce x))
                    (Frac.mul (frac_of m) (frac_of (TNonce p)))); first ring.
    by rewrite e; ring.
by move/(f_equal frac_of): ex; rewrite frac_of_TSum_empty;
  exact: (atom_frac_neq0 (t := TNonce _) I).
Qed.

(** ** The key formula *)

#[local] Lemma log_TExp_g e :
  negb (is_exp g) → negb (is_gmul g) → log g (TExp g e) = e.
Proof. by move=> gNX gNm; rewrite log_TExp_atom // bool_decide_eq_true_2. Qed.

#[local] Lemma log_hmqv_Y b t_b P_a P_b X_b :
  log b (hmqv_Y t_b P_a P_b X_b) =
  TSum {[+ log b X_b; TMul {[+ log b P_b; hmqv_m t_b X_b P_a +]} +]}.
Proof. by rewrite log_TGMul2 log_TExp. Qed.

#[local] Lemma log_hmqv_K b t_a t_b p_a x_a P_a X_a P_b X_b :
  log b (hmqv_K t_a t_b p_a x_a P_a X_a P_b X_b) =
  TMul {[+ log b (hmqv_Y t_b P_a P_b X_b);
           hmqv_s (hmqv_m t_a X_a P_b) p_a x_a +]}.
Proof. exact: log_TExp. Qed.

#[local] Lemma free_log_hmqv_Y t X P b t_b P_a P_b X_b :
  hmqv_m t X P ∉ atoms (log b X_b) → hmqv_m t X P ∉ atoms (log b P_b) →
  hmqv_m t X P ≠ hmqv_m t_b X_b P_a →
  hmqv_m t X P ∉ atoms (log b (hmqv_Y t_b P_a P_b X_b)).
Proof.
move=> hX hP hm; rewrite log_hmqv_Y; apply: not_elem_of_atoms_TSum2 hX _.
by apply: not_elem_of_atoms_TMul2 hP _;
  apply: not_elem_of_atoms_atom; [exact: hmqv_m_Nmod|].
Qed.

#[local] Lemma free_log_hmqv_K t X P b t_a t_b (p_a x_a : nonce)
    P_a X_a P_b X_b :
  hmqv_m t X P ∉ atoms (log b X_b) → hmqv_m t X P ∉ atoms (log b P_b) →
  hmqv_m t X P ≠ hmqv_m t_b X_b P_a → hmqv_m t X P ≠ hmqv_m t_a X_a P_b →
  hmqv_m t X P ∉ atoms (log b (hmqv_K t_a t_b p_a x_a P_a X_a P_b X_b)).
Proof.
move=> hX hP hB hA; rewrite log_hmqv_K.
apply: not_elem_of_atoms_TMul2; first exact: free_log_hmqv_Y.
by apply: free_hmqv_s => //; exact: hmqv_m_Nmod.
Qed.

#[local] Lemma hmqv_Y_honest t_b P_a p_b x_b :
  hmqv_Y t_b P_a (TExp g p_b) (TExp g x_b)
  = TExp g (hmqv_s (hmqv_m t_b (TExp g x_b) P_a) p_b x_b).
Proof.
by rewrite /hmqv_Y TExpA /hmqv_s TExp_TSum2 (comm (⊎) {[+ p_b +]}).
Qed.

Lemma hmqv_K_sym t_a t_b p_a x_a p_b x_b :
  hmqv_K t_a t_b p_a x_a (TExp g p_a) (TExp g x_a) (TExp g p_b) (TExp g x_b)
  = hmqv_K t_b t_a p_b x_b (TExp g p_b) (TExp g x_b) (TExp g p_a) (TExp g x_a).
Proof. by rewrite /hmqv_K !hmqv_Y_honest !TExpA (comm (⊎)). Qed.

(** If the shared secret [hmqv_K] degenerates to the group identity, then so
    does the base [hmqv_Y] the party exponentiates, whatever the (unvetted)
    peer keys [P_b] and [X_b] were. *)
Lemma hmqv_K_unit t_a t_b (p_a x_a : nonce) P_a X_a P_b X_b :
  hmqv_K t_a t_b p_a x_a P_a X_a P_b X_b = TGMul ∅ →
  hmqv_Y t_b P_a P_b X_b = TGMul ∅.
Proof.
move=> eK; apply: log_eq0 => b; apply: frac_of_eq0.
move/(f_equal (λ u, frac_of (log b u))): eK.
rewrite /= log_unit log_hmqv_K frac_of_TMul2 frac_of_TSum_empty => e.
exact: Frac.mul_eq0_l _ _ e (@hmqv_s_neq0 _ _ _ _ _).
Qed.

(** If two peer ephemerals [X_b], [X_b'] yield the same session key against the
    same claimed [P_b], the initiator exponentiated the same base [hmqv_Y]: the
    key determines that base. *)
Lemma hmqv_K_inj_base t_a t_b (p_a x_a : nonce) P_a X_a P_b X_b X_b' :
  hmqv_K t_a t_b p_a x_a P_a X_a P_b X_b
  = hmqv_K t_a t_b p_a x_a P_a X_a P_b X_b' →
  hmqv_Y t_b P_a P_b X_b = hmqv_Y t_b P_a P_b X_b'.
Proof.
move=> eK; apply: log_inj => b; apply: frac_of_inj.
move/(f_equal (λ u, frac_of (log b u))): eK.
rewrite /= !log_hmqv_K !frac_of_TMul2.
exact: Frac.mul_inj_r _ _ _ (@hmqv_s_neq0 _ _ _ _ _).
Qed.

Lemma hmqv_K_neq_unit t_a t_b (p_a x_a p_b : nonce) P_a X_a X_b :
  negb (is_exp g) → negb (is_gmul g) →
  hmqv_K t_a t_b p_a x_a P_a X_a (TExp g p_b) X_b ≠ TGMul ∅.
Proof.
move=> gNX gNm /hmqv_K_unit /(f_equal (log g)).
rewrite log_unit log_hmqv_Y log_TExp_g //.
set m := hmqv_m t_b X_b P_a => e.
have [_ ep] : log g X_b = TSum ∅ ∧ TNonce p_b = TSum ∅.
  apply: (frac_lin (h := m)); try exact: not_elem_of_atoms_TSum_empty.
  - exact: hmqv_m_Nmod.
  - exact: log_small (tsize_hmqv_m_lt _ _ _).
  - exact: free_nonce.
  - move/(f_equal frac_of): e.
    rewrite frac_of_TSum Frac.ssum_disj_union !Frac.ssum_singleton.
    by rewrite frac_of_TMul2 !frac_of_TSum_empty => ->; ring.
by move/(f_equal frac_of): ep; rewrite frac_of_TSum_empty;
  exact: (atom_frac_neq0 (t := TNonce _) I).
Qed.

(** *** Comparing coefficients of a multiplier *)

(** A multiplier that the base and the other key avoid: its coefficient
    [y⋅p_a] vanishes, so the base is [1]. *)
#[local] Lemma hmqv_K_own t_a t_b (p_a x_a : nonce) P_a X_a P_b X_b K' :
  (∀ b, hmqv_m t_a X_a P_b ∉ atoms (log b (hmqv_Y t_b P_a P_b X_b))) →
  (∀ b, hmqv_m t_a X_a P_b ∉ atoms (log b K')) →
  hmqv_K t_a t_b p_a x_a P_a X_a P_b X_b = K' →
  hmqv_K t_a t_b p_a x_a P_a X_a P_b X_b = TGMul ∅.
Proof.
move=> hY hK' eK.
set m := hmqv_m t_a X_a P_b in hY hK' eK *.
enough (E : hmqv_Y t_b P_a P_b X_b = TGMul ∅).
  by rewrite /hmqv_K E TExp_gunit.
apply: log_eq0 => b.
set y := log b (hmqv_Y t_b P_a P_b X_b) in hY *.
have [_ e] : TMul {[+ y; TNonce x_a +]} = log b K' ∧
             TMul {[+ y; TNonce p_a +]} = TSum ∅.
  apply: (frac_lin (h := m)).
  - exact: hmqv_m_Nmod.
  - by apply: not_elem_of_atoms_TMul2 (hY b) _; exact: free_nonce.
  - by apply: not_elem_of_atoms_TMul2 (hY b) _; exact: free_nonce.
  - exact: hK'.
  - exact: not_elem_of_atoms_TSum_empty.
  - move/(f_equal (λ u, frac_of (log b u))): eK.
    rewrite /= log_hmqv_K -/m -/y frac_of_TMul2 frac_hmqv_s => <-.
    by rewrite !frac_of_TMul2 frac_of_TSum_empty; ring.
apply: frac_of_eq0; move/(f_equal frac_of): e.
rewrite frac_of_TMul2 frac_of_TSum_empty => e.
exact: Frac.mul_eq0_l _ _ e (atom_frac_neq0 (t := TNonce _) I).
Qed.

(** An unmatched peer multiplier that the other key and the claimed peer key
    avoid: its coefficient [β⋅σ] vanishes, so the claimed key is [1]. *)
#[local] Lemma hmqv_K_peer t_a t_b (p_a x_a : nonce) P_a X_a P_b X_b K' :
  t_a ≠ t_b →
  (∀ b, hmqv_m t_b X_b P_a ∉ atoms (log b P_b)) →
  (∀ b, hmqv_m t_b X_b P_a ∉ atoms (log b K')) →
  hmqv_K t_a t_b p_a x_a P_a X_a P_b X_b = K' → P_b = TGMul ∅.
Proof.
move=> tab hP hK' eK; apply: log_eq0 => b.
set m := hmqv_m t_b X_b P_a in hP hK' eK *.
set s := hmqv_s (hmqv_m t_a X_a P_b) p_a x_a.
have hs : m ∉ atoms s.
  apply: free_hmqv_s; last exact: hmqv_m_Nmod.
  by case/hmqv_m_inj => e _; apply: tab; rewrite e.
have hX : m ∉ atoms (log b X_b) by apply: log_small; exact: tsize_hmqv_m_lt.
have [_ e] : TMul {[+ log b X_b; s +]} = log b K' ∧
             TMul {[+ log b P_b; s +]} = TSum ∅.
  apply: (frac_lin (h := m)).
  - exact: hmqv_m_Nmod.
  - exact: not_elem_of_atoms_TMul2.
  - exact: not_elem_of_atoms_TMul2 (hP b) hs.
  - exact: hK'.
  - exact: not_elem_of_atoms_TSum_empty.
  - move/(f_equal (λ u, frac_of (log b u))): eK.
    rewrite /= log_hmqv_K log_hmqv_Y -/m -/s => <-.
    rewrite !frac_of_TMul2 frac_of_TSum Frac.ssum_disj_union.
    by rewrite !Frac.ssum_singleton frac_of_TMul2 frac_of_TSum_empty; ring.
apply: frac_of_eq0; move/(f_equal frac_of): e.
rewrite frac_of_TMul2 frac_of_TSum_empty => e.
exact: Frac.mul_eq0_l _ _ e (@hmqv_s_neq0 _ _ _ _ _).
Qed.


(** A non-trivial session key does NOT bind an *unvetted* peer long-term key.
    Take a degenerate [P_b = 1] on one side and, on the other, a reflected
    ephemeral [X_b' = g^x_a] with [P_b'] chosen so that both keys raise [g] to
    the same two scalars, in different orders.  Then two distinct peer-key
    pairs produce the same key, which is moreover [≠ 1].  So excluding a
    trivial key does not suffice to bind an unvetted peer; the collision uses
    [P_b = 1], and excluding that too gives the binding of [hmqv_K_inj]. *)
Lemma hmqv_K_inj_counterexample t_a t_b (p_a x_a : nonce) P_a X_a :
  negb (is_gmul g) →
  let m_a  := hmqv_m t_a X_a (TGMul ∅) in
  let X_b' := TExp g (TNonce x_a) in
  let m_b' := hmqv_m t_b X_b' P_a in
  let P_b' := TExp g (TMul {[+ m_a; TNonce p_a; TInv m_b' +]}) in
  let m_a' := hmqv_m t_a X_a P_b' in
  let X_b  := TExp g (hmqv_s m_a' p_a x_a) in
  hmqv_K t_a t_b p_a x_a P_a X_a (TGMul ∅) X_b
    = hmqv_K t_a t_b p_a x_a P_a X_a P_b' X_b'
  ∧ hmqv_K t_a t_b p_a x_a P_a X_a (TGMul ∅) X_b ≠ TGMul ∅.
Proof.
move=> gNm m_a X_b' m_b' P_b' m_a' X_b.
have nb : frac_of m_b' ≠ Frac.zero.
  by apply: atom_frac_neq0; exact: hmqv_m_Nmod.
have HP : TExp P_b' m_b' = TExp g (TMul {[+ m_a; TNonce p_a +]}).
  rewrite /P_b' TExpA; congr TExp; apply: frac_of_inj.
  rewrite !frac_of_TMul2 frac_of_TMul Frac.sprod_disj_union; last first.
    move=> x _ /SMS.elem_of_singleton ->.
    exact: frac_of_TInv_neq0.
  rewrite Frac.sprod_pair Frac.sprod_singleton frac_of_TInv.
  by field.
have HY1 : hmqv_Y t_b P_a (TGMul ∅) X_b = X_b.
  by rewrite /hmqv_Y TExp_gunit TGMul_unit_r.
have HY2 : hmqv_Y t_b P_a P_b' X_b' = TExp g (hmqv_s m_a p_a x_a).
  by rewrite /hmqv_Y -/m_b' HP /hmqv_s TExp_TSum2.
split.
- by rewrite /hmqv_K -/m_a -/m_a' HY1 HY2 /X_b !TExpA (comm (⊎)).
- move=> /hmqv_K_unit; rewrite HY1 => /TExp_unit_inv E.
  exact: (Ngmul_neq_unit gNm) (E (@hmqv_s_neq0 _ _ _ _ _)).
Qed.

(** *** Binding the own multiplier

    Equal keys of the same role have the same own multiplier: otherwise
    the largest multiplier is unmatched, and every public input is smaller
    than the multiplier that hashes it. *)

#[local] Lemma hmqv_K_maxA t_a t_b (p_a x_a p_a' x_a' : nonce)
    P_a X_a P_b X_b P_a' X_a' P_b' X_b' :
  t_a ≠ t_b →
  hmqv_m t_a X_a P_b ≠ hmqv_m t_a X_a' P_b' →
  tsize (hmqv_m t_a X_a' P_b') ≤ tsize (hmqv_m t_a X_a P_b) →
  tsize (hmqv_m t_b X_b P_a) ≤ tsize (hmqv_m t_a X_a P_b) →
  tsize (hmqv_m t_b X_b' P_a') ≤ tsize (hmqv_m t_a X_a P_b) →
  hmqv_K t_a t_b p_a x_a P_a X_a P_b X_b ≠ TGMul ∅ →
  hmqv_K t_a t_b p_a x_a P_a X_a P_b X_b
  = hmqv_K t_a t_b p_a' x_a' P_a' X_a' P_b' X_b' → False.
Proof.
move=> tab nA lA' lB lB' nK eK.
have tags X P X' P' : hmqv_m t_a X P ≠ hmqv_m t_b X' P' by case/hmqv_m_inj.
have := tsize_hmqv_m_lt t_b X_b P_a; have := tsize_hmqv_m_lt t_b X_b' P_a'.
have := tsize_hmqv_m_lt2 t_a X_a P_b; have := tsize_hmqv_m_lt2 t_a X_a' P_b'.
move=> lP' lP lX' lX.
apply: nK; apply: (hmqv_K_own _ _ eK) => b.
- by apply: free_log_hmqv_Y; [apply: log_small; lia|apply: log_small; lia|].
- apply: free_log_hmqv_K => //; by apply: log_small; lia.
Qed.

#[local] Lemma hmqv_K_maxB t_a t_b (p_a x_a p_a' x_a' : nonce)
    P_a X_a P_b X_b P_a' X_a' P_b' X_b' :
  t_a ≠ t_b → P_b ≠ TGMul ∅ → P_b' ≠ TGMul ∅ →
  hmqv_m t_a X_a P_b ≠ hmqv_m t_a X_a' P_b' →
  tsize (hmqv_m t_a X_a P_b) ≤ tsize (hmqv_m t_b X_b P_a) →
  tsize (hmqv_m t_a X_a' P_b') ≤ tsize (hmqv_m t_b X_b P_a) →
  tsize (hmqv_m t_b X_b' P_a') ≤ tsize (hmqv_m t_b X_b P_a) →
  hmqv_K t_a t_b p_a x_a P_a X_a P_b X_b
  = hmqv_K t_a t_b p_a' x_a' P_a' X_a' P_b' X_b' → False.
Proof.
move=> tab nP nP' nA lA lA' lB' eK.
have tags X P X' P' : hmqv_m t_a X P ≠ hmqv_m t_b X' P' by case/hmqv_m_inj.
have lX := tsize_hmqv_m_lt t_b X_b P_a.
have lX' := tsize_hmqv_m_lt t_b X_b' P_a'.
have lP := tsize_hmqv_m_lt2 t_a X_a P_b.
have lP' := tsize_hmqv_m_lt2 t_a X_a' P_b'.
case: (decide (hmqv_m t_b X_b P_a = hmqv_m t_b X_b' P_a')) => [eB|nB];
    last first.
  apply: nP; apply: (hmqv_K_peer tab _ _ eK) => b.
    by apply: log_small; lia.
  apply: free_log_hmqv_K.
  - by apply: log_small; lia.
  - by apply: log_small; lia.
  - exact: nB.
  - exact: not_eq_sym (tags _ _ _ _).
case/hmqv_m_inj: (eB) => _ [eXb ePa]; subst X_b' P_a'.
set B := hmqv_m t_b X_b P_a in eB lA lA' lB' lX *.
set s := hmqv_s (hmqv_m t_a X_a P_b) p_a x_a.
set s' := hmqv_s (hmqv_m t_a X_a' P_b') p_a' x_a'.
(* The linear coefficients in [B] agree. *)
have part b : TMul {[+ log b P_b; s +]} = TMul {[+ log b P_b'; s' +]}.
  have hs : B ∉ atoms s.
    apply: free_hmqv_s; [exact: not_eq_sym (tags _ _ _ _)|exact: hmqv_m_Nmod].
  have hs' : B ∉ atoms s'.
    apply: free_hmqv_s; [exact: not_eq_sym (tags _ _ _ _)|exact: hmqv_m_Nmod].
  have hX : B ∉ atoms (log b X_b) by apply: log_small; lia.
  have [_ e] : TMul {[+ log b X_b; s +]} = TMul {[+ log b X_b; s' +]} ∧
               TMul {[+ log b P_b; s +]} = TMul {[+ log b P_b'; s' +]}.
    apply: (frac_lin (h := B)).
    - exact: hmqv_m_Nmod.
    - exact: not_elem_of_atoms_TMul2.
    - by apply: not_elem_of_atoms_TMul2 => //; apply: log_small; lia.
    - exact: not_elem_of_atoms_TMul2.
    - by apply: not_elem_of_atoms_TMul2 => //; apply: log_small; lia.
    - move/(f_equal (λ u, frac_of (log b u))): eK.
      rewrite /= !log_hmqv_K !log_hmqv_Y !frac_of_TMul2 !frac_of_TSum.
      rewrite !Frac.ssum_disj_union !Frac.ssum_singleton !frac_of_TMul2.
      rewrite ?frac_hmqv_s => e; rewrite /B.
      by apply: (eq_trans _ (eq_trans e _)); ring.
  exact: e.
(* Comparing the linear coefficients in the larger own multiplier makes a
   claimed peer key [1]. *)
have key X P X' P' (p x p' x' : nonce) Q Q' :
    hmqv_m t_a X P ≠ hmqv_m t_a X' P' →
    tsize Q < tsize (hmqv_m t_a X P) → tsize Q' < tsize (hmqv_m t_a X P) →
    (∀ b, TMul {[+ log b Q; hmqv_s (hmqv_m t_a X P) p x +]}
          = TMul {[+ log b Q'; hmqv_s (hmqv_m t_a X' P') p' x' +]}) →
    Q = TGMul ∅.
  move=> nA' lQ lQ' E; apply: log_eq0 => b.
  set A := hmqv_m t_a X P in nA' lQ lQ' E *.
  have [_ e] : TMul {[+ log b Q; TNonce x +]} =
               TMul {[+ log b Q'; hmqv_s (hmqv_m t_a X' P') p' x' +]} ∧
               TMul {[+ log b Q; TNonce p +]} = TSum ∅.
    apply: (frac_lin (h := A)).
    - exact: hmqv_m_Nmod.
    - by apply: not_elem_of_atoms_TMul2; [apply: log_small|exact: free_nonce].
    - by apply: not_elem_of_atoms_TMul2; [apply: log_small|exact: free_nonce].
    - apply: not_elem_of_atoms_TMul2; first by apply: log_small.
      by apply: free_hmqv_s; [|exact: hmqv_m_Nmod].
    - exact: not_elem_of_atoms_TSum_empty.
    - move/(f_equal frac_of): (E b); rewrite !frac_of_TMul2 frac_hmqv_s => <-.
      by rewrite frac_of_TSum_empty; ring.
  apply: frac_of_eq0; move/(f_equal frac_of): e.
  rewrite frac_of_TMul2 frac_of_TSum_empty => e.
  exact: Frac.mul_eq0_l _ _ e (atom_frac_neq0 (t := TNonce _) I).
case: (Nat.le_ge_cases (tsize (hmqv_m t_a X_a' P_b'))
                       (tsize (hmqv_m t_a X_a P_b))) => le.
- apply: nP.
  by apply: (key _ _ _ _ p_a x_a p_a' x_a' P_b P_b' nA _ _ part); lia.
- apply: nP'.
  apply: (key _ _ _ _ p_a' x_a' p_a x_a P_b' P_b (not_eq_sym nA)); try lia.
  by move=> b; rewrite part.
Qed.

#[local] Lemma hmqv_K_own_match t_a t_b (p_a x_a p_a' x_a' : nonce)
    P_a X_a P_b X_b P_a' X_a' P_b' X_b' :
  t_a ≠ t_b → P_b ≠ TGMul ∅ → P_b' ≠ TGMul ∅ →
  hmqv_K t_a t_b p_a x_a P_a X_a P_b X_b ≠ TGMul ∅ →
  hmqv_K t_a t_b p_a x_a P_a X_a P_b X_b
  = hmqv_K t_a t_b p_a' x_a' P_a' X_a' P_b' X_b' →
  hmqv_m t_a X_a P_b = hmqv_m t_a X_a' P_b'.
Proof.
move=> tab nP nP' nK eK.
case: (decide (hmqv_m t_a X_a P_b = hmqv_m t_a X_a' P_b')) => // nA.
exfalso.
have nK' : hmqv_K t_a t_b p_a' x_a' P_a' X_a' P_b' X_b' ≠ TGMul ∅.
  by rewrite -eK.
set a  := tsize (hmqv_m t_a X_a P_b).
set a' := tsize (hmqv_m t_a X_a' P_b').
set b  := tsize (hmqv_m t_b X_b P_a).
set b' := tsize (hmqv_m t_b X_b' P_a').
have : (a' ≤ a ∧ b ≤ a ∧ b' ≤ a) ∨ (a ≤ a' ∧ b ≤ a' ∧ b' ≤ a') ∨
       (a ≤ b ∧ a' ≤ b ∧ b' ≤ b) ∨ (a ≤ b' ∧ a' ≤ b' ∧ b ≤ b') by lia.
case=> [[h1 [h2 h3]]|[[h1 [h2 h3]]|[[h1 [h2 h3]]|[h1 [h2 h3]]]]].
- exact: hmqv_K_maxA tab nA h1 h2 h3 nK eK.
- exact: hmqv_K_maxA tab (not_eq_sym nA) h1 h3 h2 nK' (eq_sym eK).
- exact: hmqv_K_maxB tab nP nP' nA h1 h2 h3 eK.
- exact: hmqv_K_maxB tab nP' nP (not_eq_sym nA) h2 h1 h3 (eq_sym eK).
Qed.

(** The key binds the private keys and the claimed peer long-term key of a
    party with well-formed keys, though not the peer's ephemeral: a rogue
    long-term key can make two peer ephemerals give the same key for the
    same ephemeral private key.  Fresh ephemerals, or a vetted peer key
    ([hmqv_K_inj_vetted]), bind the peer's ephemeral too. *)
Lemma hmqv_K_inj t_a t_b (p_a x_a p_a' x_a' : nonce) P_b X_b P_b' X_b' :
  negb (is_exp g) → negb (is_gmul g) → t_a ≠ t_b →
  P_b ≠ TGMul ∅ → P_b' ≠ TGMul ∅ →
  hmqv_K t_a t_b p_a x_a (TExp g p_a) (TExp g x_a) P_b X_b ≠ TGMul ∅ →
  hmqv_K t_a t_b p_a x_a (TExp g p_a) (TExp g x_a) P_b X_b
  = hmqv_K t_a t_b p_a' x_a' (TExp g p_a') (TExp g x_a') P_b' X_b' →
  p_a = p_a' ∧ x_a = x_a' ∧ P_b = P_b'.
Proof.
move=> gNX gNm tab nP nP' nK eK.
have gN1 := Ngmul_neq_unit gNm.
have [_ [eX eP]] := hmqv_m_inj (hmqv_K_own_match tab nP nP' nK eK).
move/(TExp_injr gN1): eX => - [] ex; subst x_a' P_b'.
split; last by [].
case: (decide (p_a = p_a')) => // np; exfalso.
have tags X P X' P' : hmqv_m t_a X P ≠ hmqv_m t_b X' P' by case/hmqv_m_inj.
have nB : hmqv_m t_b X_b (TExp g p_a) ≠ hmqv_m t_b X_b' (TExp g p_a').
  by case/hmqv_m_inj => _ [_ /(TExp_injr gN1) [] e]; apply: np.
have lX := tsize_hmqv_m_lt t_b X_b (TExp g p_a).
have lX' := tsize_hmqv_m_lt t_b X_b' (TExp g p_a').
have lP := tsize_hmqv_m_lt2 t_a (TExp g x_a) P_b.
have : (tsize (hmqv_m t_b X_b (TExp g p_a)) ≤
          tsize (hmqv_m t_a (TExp g x_a) P_b) ∧
        tsize (hmqv_m t_b X_b' (TExp g p_a')) ≤
          tsize (hmqv_m t_a (TExp g x_a) P_b)) ∨
       (tsize (hmqv_m t_a (TExp g x_a) P_b) ≤
          tsize (hmqv_m t_b X_b (TExp g p_a)) ∧
        tsize (hmqv_m t_b X_b' (TExp g p_a')) ≤
          tsize (hmqv_m t_b X_b (TExp g p_a))) ∨
       (tsize (hmqv_m t_a (TExp g x_a) P_b) ≤
          tsize (hmqv_m t_b X_b' (TExp g p_a')) ∧
        tsize (hmqv_m t_b X_b (TExp g p_a)) ≤
          tsize (hmqv_m t_b X_b' (TExp g p_a'))) by lia.
case=> [[h1 h2]|[[h1 h2]|[h1 h2]]].
- (* The own multiplier is the largest: comparing its coefficients cancels
     the base. *)
  apply: nK.
  enough (E : hmqv_Y t_b (TExp g p_a) P_b X_b = TGMul ∅).
    by rewrite /hmqv_K E TExp_gunit.
  apply: log_eq0 => b.
  have fy : hmqv_m t_a (TExp g x_a) P_b ∉
            atoms (log b (hmqv_Y t_b (TExp g p_a) P_b X_b)).
    apply: free_log_hmqv_Y; [apply: log_small; lia|exact: log_small|].
    exact: tags.
  have fy' : hmqv_m t_a (TExp g x_a) P_b ∉
             atoms (log b (hmqv_Y t_b (TExp g p_a') P_b X_b')).
    apply: free_log_hmqv_Y; [apply: log_small; lia|exact: log_small|].
    exact: tags.
  set A := hmqv_m t_a (TExp g x_a) P_b in fy fy' eK *.
  set y := log b (hmqv_Y t_b (TExp g p_a) P_b X_b) in fy *.
  set y' := log b (hmqv_Y t_b (TExp g p_a') P_b X_b') in fy' *.
  have [e0 e1] : TMul {[+ y; TNonce x_a +]} = TMul {[+ y'; TNonce x_a +]} ∧
                 TMul {[+ y; TNonce p_a +]} = TMul {[+ y'; TNonce p_a' +]}.
    apply: (frac_lin (h := A)).
    - exact: hmqv_m_Nmod.
    - by apply: not_elem_of_atoms_TMul2 => //; exact: free_nonce.
    - by apply: not_elem_of_atoms_TMul2 => //; exact: free_nonce.
    - by apply: not_elem_of_atoms_TMul2 => //; exact: free_nonce.
    - by apply: not_elem_of_atoms_TMul2 => //; exact: free_nonce.
    - move/(f_equal (λ u, frac_of (log b u))): eK.
      rewrite /= !log_hmqv_K -/A -/y -/y' !frac_of_TMul2 !frac_hmqv_s => e.
      by apply: (eq_trans _ (eq_trans e _)); ring.
  have eyy : frac_of y = frac_of y'.
    move/(f_equal frac_of): e0; rewrite !frac_of_TMul2.
    exact: Frac.mul_inj_r _ _ _ (atom_frac_neq0 (t := TNonce _) I).
  apply: frac_of_eq0; move/(f_equal frac_of): e1;
    rewrite !frac_of_TMul2 -eyy => e1.
  case: (decide (frac_of y = Frac.zero)) => // ny.
  exfalso; apply: np.
  have : frac_of (TNonce p_a) = frac_of (TNonce p_a').
    rewrite (comm Frac.mul (frac_of y)) (comm Frac.mul (frac_of y)) in e1.
    exact: Frac.mul_inj_r _ _ _ ny e1.
  by move/frac_of_inj => - [].
- (* The peer multiplier of the first key is the largest and unmatched. *)
  apply: nP; apply: (hmqv_K_peer tab _ _ eK) => b.
    by apply: log_small; lia.
  apply: free_log_hmqv_K.
  + by apply: log_small; lia.
  + by apply: log_small; lia.
  + exact: nB.
  + exact: not_eq_sym (tags _ _ _ _).
- (* The peer multiplier of the second key is the largest and unmatched. *)
  apply: nP; apply: (hmqv_K_peer tab _ _ (eq_sym eK)) => b.
    by apply: log_small; lia.
  apply: free_log_hmqv_K.
  + by apply: log_small; lia.
  + by apply: log_small; lia.
  + exact: not_eq_sym nB.
  + exact: not_eq_sym (tags _ _ _ _).
Qed.

Lemma hmqv_K_inj_vetted t_a t_b (p_a x_a p_a' x_a' p_b p_b' : nonce) X_b X_b' :
  negb (is_exp g) → negb (is_gmul g) → t_a ≠ t_b →
  hmqv_K t_a t_b p_a x_a (TExp g p_a) (TExp g x_a) (TExp g p_b) X_b
  = hmqv_K t_a t_b p_a' x_a' (TExp g p_a') (TExp g x_a') (TExp g p_b') X_b' →
  p_a = p_a' ∧ x_a = x_a' ∧ p_b = p_b' ∧ X_b = X_b'.
Proof.
move=> gNX gNm tab eK.
have gN1 := Ngmul_neq_unit gNm.
have nP (p : nonce) : TExp g p ≠ TGMul ∅.
  exact: Ngmul_neq_unit (Ngmul_TExp gNm (mono_num_atom (TNonce p) I)).
have [ep [ex eP]] :=
  hmqv_K_inj gNX gNm tab (nP _) (nP _) (hmqv_K_neq_unit gNX gNm) eK.
subst p_a' x_a'.
move/(TExp_injr gN1): (eP) => - [] epb; subst p_b'.
do 3!split=> //.
have eY := hmqv_K_inj_base eK.
set B := hmqv_m t_b X_b (TExp g p_a) in eY.
set B' := hmqv_m t_b X_b' (TExp g p_a) in eY.
case: (decide (B = B')) => [/hmqv_m_inj [_ [? _]] //|nB]; exfalso.
move/(f_equal (log g)): eY; rewrite !log_hmqv_Y !log_TExp_g // -/B -/B' => eY.
have lX := tsize_hmqv_m_lt t_b X_b (TExp g p_a).
have lX' := tsize_hmqv_m_lt t_b X_b' (TExp g p_a).
have key X X' (C C' : term) :
    C ≠ C' → negb (is_mod C) → negb (is_mod C') → tsize C' ≤ tsize C →
    tsize X < tsize C → tsize X' < tsize C' →
    (∀ (n : nonce), C ≠ TNonce n) → (∀ (n : nonce), C' ≠ TNonce n) →
    TSum {[+ log g X; TMul {[+ TNonce p_b; C +]} +]} =
    TSum {[+ log g X'; TMul {[+ TNonce p_b; C' +]} +]} → False.
  move=> nC mC mC' le lx lx' hC hC' E.
  have [_ e] : log g X = TSum {[+ log g X'; TMul {[+ TNonce p_b; C' +]} +]} ∧
               TNonce p_b = TSum ∅.
    apply: (frac_lin (h := C)) => //.
    - by apply: log_small; lia.
    - by apply: not_elem_of_atoms_atom => //; exact: hC.
    - apply: not_elem_of_atoms_TSum2; first by apply: log_small; lia.
      apply: not_elem_of_atoms_TMul2;
        first by apply: not_elem_of_atoms_atom => //; exact: hC.
      exact: not_elem_of_atoms_atom.
    - exact: not_elem_of_atoms_TSum_empty.
    - move/(f_equal frac_of): E.
      rewrite !frac_of_TSum !Frac.ssum_disj_union !Frac.ssum_singleton.
      rewrite Frac.ssum_empty !frac_of_TMul2 => e.
      by apply: (eq_trans _ (eq_trans e _)); ring.
  by move/(f_equal frac_of): e; rewrite frac_of_TSum_empty;
    exact: (atom_frac_neq0 (t := TNonce _) I).
case: (Nat.le_ge_cases (tsize B') (tsize B)) => le.
- by apply: (key X_b X_b' B B') => //; exact: hmqv_m_Nmod.
- by apply: (key X_b' X_b B' B (not_eq_sym nB)) => //; exact: hmqv_m_Nmod.
Qed.


(** ** Identity binding across roles *)

#[local] Lemma hmqv_K_cross_max t_a t_b (p_a x_a p_b x_b : nonce)
    P_b X_b Q_a Y_a h :
  negb (is_exp g) → negb (is_gmul g) → t_a ≠ t_b → P_b ≠ TGMul ∅ →
  hmqv_K t_a t_b p_a x_a (TExp g p_a) (TExp g x_a) P_b X_b ≠ TGMul ∅ →
  hmqv_K t_a t_b p_a x_a (TExp g p_a) (TExp g x_a) P_b X_b
  = hmqv_K t_b t_a p_b x_b (TExp g p_b) (TExp g x_b) Q_a Y_a →
  hmqv_m t_a (TExp g x_a) P_b = hmqv_m t_a Y_a (TExp g p_b) ∨
    tsize (hmqv_m t_a (TExp g x_a) P_b) ≤ tsize h ∧
    tsize (hmqv_m t_a Y_a (TExp g p_b)) ≤ tsize h →
  hmqv_m t_b X_b (TExp g p_a) = hmqv_m t_b (TExp g x_b) Q_a ∨
    tsize (hmqv_m t_b X_b (TExp g p_a)) ≤ tsize h ∧
    tsize (hmqv_m t_b (TExp g x_b) Q_a) ≤ tsize h →
  h = hmqv_m t_a (TExp g x_a) P_b ∧
    hmqv_m t_a (TExp g x_a) P_b ≠ hmqv_m t_a Y_a (TExp g p_b) ∨
  h = hmqv_m t_b X_b (TExp g p_a) ∧
    hmqv_m t_b X_b (TExp g p_a) ≠ hmqv_m t_b (TExp g x_b) Q_a →
  False.
Proof.
move=> gNX gNm tab nP nK eK hA hB hh.
have tags X X' Q Q' : hmqv_m t_a X Q ≠ hmqv_m t_b X' Q' by case/hmqv_m_inj.
have hN (n : nonce) : h ≠ TNonce n by case: hh => [[-> _]|[-> _]].
have honest b (n : nonce) : h ∉ atoms (log b (TExp g n)).
  rewrite log_TExp_atom //; case: bool_decide;
    last exact: not_elem_of_atoms_TSum_empty.
  by apply: not_elem_of_atoms_atom => //; exact: hN.
have fX b : h ∉ atoms (log b X_b).
  case: (hB) => [/hmqv_m_inj [_ [-> _]]|[lB _]]; first exact: honest.
  by apply: log_small; have := tsize_hmqv_m_lt t_b X_b (TExp g p_a); lia.
have fP b : h ∉ atoms (log b P_b).
  case: (hA) => [/hmqv_m_inj [_ [_ ->]]|[lA _]]; first exact: honest.
  by apply: log_small; have := tsize_hmqv_m_lt2 t_a (TExp g x_a) P_b; lia.
have fY b : h ∉ atoms (log b Y_a).
  case: (hA) => [/hmqv_m_inj [_ [<- _]]|[_ lA']]; first exact: honest.
  by apply: log_small; have := tsize_hmqv_m_lt t_a Y_a (TExp g p_b); lia.
have fQ b : h ∉ atoms (log b Q_a).
  case: (hB) => [/hmqv_m_inj [_ [_ <-]]|[_ lB']]; first exact: honest.
  by apply: log_small; have := tsize_hmqv_m_lt2 t_b (TExp g x_b) Q_a; lia.
case: hh => [[eh nA]|[eh nB]]; subst h.
- case: nK; apply: (hmqv_K_own _ _ eK) => b.
  + by apply: free_log_hmqv_Y (fX b) (fP b) _; exact: tags.
  + apply: free_log_hmqv_K (fY b) (fQ b) nA _.
    exact: tags.
- case: nP; apply: (hmqv_K_peer tab fP _ eK) => b.
  apply: free_log_hmqv_K (fY b) (fQ b) _ nB.
  exact: not_eq_sym (tags _ _ _ _).
Qed.

Lemma hmqv_K_inj' t_a t_b (p_a x_a p_b x_b : nonce) P_b X_b Q_a Y_a :
  negb (is_exp g) → negb (is_gmul g) → t_a ≠ t_b →
  P_b ≠ TGMul ∅ → Q_a ≠ TGMul ∅ →
  hmqv_K t_a t_b p_a x_a (TExp g p_a) (TExp g x_a) P_b X_b ≠ TGMul ∅ →
  hmqv_K t_a t_b p_a x_a (TExp g p_a) (TExp g x_a) P_b X_b
  = hmqv_K t_b t_a p_b x_b (TExp g p_b) (TExp g x_b) Q_a Y_a →
  P_b = TExp g p_b ∧ X_b = TExp g x_b ∧ Q_a = TExp g p_a ∧ Y_a = TExp g x_a.
Proof.
move=> gNX gNm tab nP nQ nK eK.
have tba : t_b ≠ t_a by congruence.
have nK' : hmqv_K t_b t_a p_b x_b (TExp g p_b) (TExp g x_b) Q_a Y_a
             ≠ TGMul ∅ by rewrite -eK.
have L h := hmqv_K_cross_max (h := h) gNX gNm tab nP nK eK.
have R h := hmqv_K_cross_max (h := h) gNX gNm tba nQ nK' (eq_sym eK).
suff : hmqv_m t_a (TExp g x_a) P_b = hmqv_m t_a Y_a (TExp g p_b) ∧
       hmqv_m t_b X_b (TExp g p_a) = hmqv_m t_b (TExp g x_b) Q_a.
  by case=> /hmqv_m_inj [_ [<- ->]] /hmqv_m_inj [_ [-> <-]].
set m_a  := hmqv_m t_a (TExp g x_a) P_b in L R *.
set m_b  := hmqv_m t_b X_b (TExp g p_a) in L R *.
set m_a' := hmqv_m t_a Y_a (TExp g p_b) in L R *.
set m_b' := hmqv_m t_b (TExp g x_b) Q_a in L R *.
case: (decide (m_a = m_a')) => eA; case: (decide (m_b = m_b')) => eB.
- by [].
- exfalso; case: (Nat.le_ge_cases (tsize m_b') (tsize m_b)) => le.
  + by apply: (L m_b); [left|right; lia|right].
  + apply: (R m_b'); [right; lia|by left; rewrite eA|left].
    by split; last exact: not_eq_sym eB.
- exfalso; case: (Nat.le_ge_cases (tsize m_a') (tsize m_a)) => le.
  + by apply: (L m_a); [right; lia|left|left].
  + apply: (R m_a'); [by left; rewrite eB|right; lia|right].
    by split; last exact: not_eq_sym eA.
- exfalso.
  have : (tsize m_b ≤ tsize m_a ∧ tsize m_a' ≤ tsize m_a ∧
          tsize m_b' ≤ tsize m_a) ∨
         (tsize m_a ≤ tsize m_b ∧ tsize m_a' ≤ tsize m_b ∧
          tsize m_b' ≤ tsize m_b) ∨
         (tsize m_a ≤ tsize m_a' ∧ tsize m_b ≤ tsize m_a' ∧
          tsize m_b' ≤ tsize m_a') ∨
         (tsize m_a ≤ tsize m_b' ∧ tsize m_b ≤ tsize m_b' ∧
          tsize m_a' ≤ tsize m_b') by lia.
  case=> [?|[?|[?|?]]].
  + by apply: (L m_a); [right; lia|right; lia|left].
  + by apply: (L m_b); [right; lia|right; lia|right].
  + apply: (R m_a'); [right; lia|right; lia|right].
    by split; last exact: not_eq_sym eA.
  + apply: (R m_b'); [right; lia|right; lia|left].
    by split; last exact: not_eq_sym eB.
Qed.


(** ** Group factors of the key

    The logarithm of the key at [g] is [(α + p_b⋅m_b)⋅σ] for a well-formed
    claimed long-term key [g^p_b], where [α] is that of the peer share and
    [σ = x_a + m_a⋅p_a].  With [D] its denominator, its numerator is the
    part [α⋅σ⋅D], free of [m_b], plus [m_b⋅p_b⋅σ⋅D].  A monomial of the second
    part with the most occurrences of [x_a] (or [p_a]) survives in the
    numerator, and gives a group factor with [x_a] (or [p_a]) and [p_b] in
    its exponent. *)

Add Ring kf_ring : (Frac.frac_ring_theory (T := PreTerm.pre_term)).
Add Field kf_field : (Frac.frac_field_theory (T := PreTerm.pre_term)).
Add Ring kf_pring : (Poly.poly_ring_theory (T := PreTerm.pre_term)).

#[local] Lemma lin_parts (r A : Frac.frac PreTerm.pre_term)
    (Q S : Poly.poly PreTerm.pre_term) y :
  Frac.all_vars (λ z, z ≠ y) A →
  (∀ m, m ∈ Poly.car Q → y ∉ m) → (∀ m, m ∈ Poly.car S → y ∉ m) →
  r = Frac.mul (Frac.add A (Frac.mul (Frac.of_poly Q)
                                     (Frac.of_poly (Poly.var y))))
               (Frac.of_poly S) →
  (∀ m, m ∈ Poly.car (Frac.den r) → y ∉ m) ∧
  (∀ ρ, ρ ∈ Poly.car (Q * (S * Frac.den r))%P →
        ({[+ y +]} ⊎ ρ) ∈ Poly.car (Frac.num r)) ∧
  ∃ P0, Frac.of_poly P0 = Frac.mul A (Frac.of_poly (S * Frac.den r)%P) ∧
        ∀ ρ, ρ ∈ Poly.car P0 → ρ ∈ Poly.car (Frac.num r).
Proof.
move=> hA hQ hS er.
set D := Frac.den r; set Nn := Frac.num r.
have nD : D ≠ Poly.zero := Frac.den_neq0 r.
have no1 p : y ∉ Poly.vars (Frac.den (Frac.of_poly p)).
  rewrite Frac.den_of_poly Poly.oneE => /Poly.elem_of_vars [n [+ yn]].
  rewrite Poly.car_mono => /SMS.elem_of_singleton en; rewrite en in yn.
  by case: (MSet.not_elem_of_empty _ yn).
have Dfree : ∀ m, m ∈ Poly.car D → y ∉ m.
  move=> m mD ym.
  have yD : y ∈ Poly.vars (Frac.den r) by apply/Poly.elem_of_vars; exists m.
  rewrite er in yD.
  case: (Frac.vars_den_mul _ _ _ yD) => [yAQ|yS]; last exact: no1 yS.
  case: (Frac.vars_den_add _ _ _ yAQ) => [yA|yQ].
  - have := proj1 (Frac.all_vars_iff _ _) hA y.
    by apply; rewrite // /Frac.vars; apply/elem_of_app; right.
  - by move: yQ; rewrite -Frac.of_poly_mul; apply: no1.
have poly_free p : (∀ m, m ∈ Poly.car p → y ∉ m) →
    Frac.all_vars (λ z, z ≠ y) (Frac.of_poly p).
  move=> hp m x [mp|mp] xm ex; subst x.
  - by move: mp; rewrite Frac.num_of_poly => /hp.
  - move: mp; rewrite Frac.den_of_poly Poly.oneE Poly.car_mono.
    move=> /SMS.elem_of_singleton em; rewrite em in xm.
    by case: (MSet.not_elem_of_empty _ xm).
have nD' : Frac.of_poly D ≠ Frac.zero.
  move=> e; apply: nD; move/(f_equal Frac.num): e.
  by rewrite Frac.num_of_poly Frac.num_zero.
have eN : Frac.of_poly Nn = Frac.mul r (Frac.of_poly D).
  rewrite -(Frac.make_num_den r) Frac.make_div -/Nn -/D Frac.divE.
  by field.
set P1 := (Q * (S * D))%P.
set P0 := (Nn + - (Poly.mono {[+ y +]} * P1))%P.
have eNP : Nn = (P0 + Poly.mono {[+ y +]} * P1)%P by rewrite /P0; ring.
have eP0 : Frac.of_poly P0 = Frac.mul A (Frac.of_poly (S * D)%P).
  rewrite /P0 /P1 Frac.of_poly_add Frac.of_poly_opp !Frac.of_poly_mul eN er.
  by rewrite -Poly.varE; ring.
have P0free : ∀ ρ, ρ ∈ Poly.car P0 → y ∉ ρ.
  have : Frac.all_vars (λ z, z ≠ y) (Frac.of_poly P0).
    rewrite eP0; apply: Frac.all_vars_mul hA _.
    rewrite Frac.of_poly_mul; apply: Frac.all_vars_mul; exact: poly_free.
  move=> h ρ ρP yρ; apply: (h ρ y) => //; left; by rewrite Frac.num_of_poly.
split=> //; split.
  move=> ρ ρP1; apply/Poly.coeff_neq0_elem.
  rewrite eNP Poly.coeff_add Poly.coeff_mono_mul_in.
  have -> : Poly.coeff ({[+ y +]} ⊎ ρ) P0 = 0%Z.
    case: (decide (Poly.coeff ({[+ y +]} ⊎ ρ) P0 = 0%Z)) => //.
    move=> /Poly.coeff_neq0_elem /P0free []; apply/MSet.elem_of_disj_union.
    by left; apply/MSet.elem_of_singleton.
  by rewrite Z.add_0_l; apply/Poly.coeff_neq0_elem.
exists P0; split=> // ρ ρP; apply/Poly.coeff_neq0_elem.
rewrite eNP Poly.coeff_add (Poly.coeff_mono_mul_out {[+ y +]} ρ _ y) ?Z.add_0_r.
- exact/Poly.coeff_neq0_elem.
- exact/MSet.elem_of_singleton.
- exact: P0free.
Qed.

#[local] Lemma car_scalar (x m p : PreTerm.pre_term) n :
  n ∈ Poly.car (Poly.var x + Poly.var m * Poly.var p)%P →
  n = {[+ x +]} ∨ n = {[+ m +]} ⊎ {[+ p +]}.
Proof.
rewrite Poly.car_add !Poly.varE Poly.mul_mono !Poly.car_mono.
by case/SMS.elem_of_disj_union => /SMS.elem_of_singleton; tauto.
Qed.

#[local] Lemma coeff_scalar (x m p : PreTerm.pre_term) n :
  x ≠ m → (n = {[+ x +]} ∨ n = {[+ m +]} ⊎ {[+ p +]}) →
  Poly.coeff n (Poly.var x + Poly.var m * Poly.var p)%P ≠ 0%Z.
Proof.
move=> xm hn.
have ne : ({[+ x +]} : MSet.mset PreTerm.pre_term) ≠ {[+ m +]} ⊎ {[+ p +]}.
  move/(f_equal (MSet.count m)); rewrite MSet.count_disj_union.
  rewrite !MSet.count_singleton bool_decide_eq_false_2 1?bool_decide_eq_true_2;
    [lia|done|exact: not_eq_sym].
rewrite Poly.coeff_add !Poly.varE Poly.mul_mono !Poly.coeff_mono.
case: hn => ->.
- by rewrite bool_decide_eq_true_2 // bool_decide_eq_false_2.
- rewrite bool_decide_eq_false_2; last exact: not_eq_sym.
  by rewrite bool_decide_eq_true_2.
Qed.

#[local] Lemma hmqv_K_gfactor_peer t_a t_b (p_a x_a p_b a : nonce) P_a X_a X_b :
  negb (is_exp g) → negb (is_gmul g) → t_a ≠ t_b → a = x_a ∨ a = p_a →
  ∃ u, u ∈ gfactors (hmqv_K t_a t_b p_a x_a P_a X_a (TExp g p_b) X_b) ∧
       {[+ TNonce a; TNonce p_b +]} ⊆ SMS.pos (exps u).
Proof.
move=> gNX gNm tab ha.
set K := hmqv_K t_a t_b p_a x_a P_a X_a (TExp g p_b) X_b.
set mA := hmqv_m t_a X_a (TExp g p_b).
set mB := hmqv_m t_b X_b P_a.
set y := unfold_term mB.
set ux := unfold_term (TNonce x_a); set up := unfold_term (TNonce p_a).
set ub := unfold_term (TNonce p_b); set ua := unfold_term (TNonce a).
set um := unfold_term mA.
set sp := (Poly.var ux + Poly.var um * Poly.var up)%P.
set r := dh_map K !!! unfold_term g.
have hash_nonce (n : nonce) t X P : unfold_term (hmqv_m t X P) ≠
                                    unfold_term (TNonce n).
  by move/unfold_term_inj.
have yum : y ≠ um.
  by move/unfold_term_inj/hmqv_m_inj => [] e _; apply: tab.
have er : r = Frac.mul (Frac.add (pre_frac (log g X_b))
                         (Frac.mul (Frac.of_poly (Poly.var ub))
                                   (Frac.of_poly (Poly.var y))))
                       (Frac.of_poly sp).
  rewrite /r -pre_frac_log /K log_hmqv_K log_hmqv_Y log_TExp_g //.
  rewrite pre_frac_TMul2 pre_frac_TSum2 pre_frac_TMul2 /hmqv_s pre_frac_TSum2
    pre_frac_TMul2.
  rewrite (pre_frac_atom (a := TNonce p_b)) // (pre_frac_atom (a := mB));
    last exact: hmqv_m_Nmod.
  rewrite (pre_frac_atom (a := TNonce x_a)) // (pre_frac_atom (a := TNonce p_a))
    //.
  rewrite (pre_frac_atom (a := mA)); last exact: hmqv_m_Nmod.
  by rewrite /sp Frac.of_poly_add Frac.of_poly_mul.
have hA : Frac.all_vars (λ z, z ≠ y) (pre_frac (log g X_b)).
  by apply: not_elem_of_atoms_pre_frac; apply: log_small;
    exact: tsize_hmqv_m_lt.
have hQ : ∀ m, m ∈ Poly.car (Poly.var ub) → y ∉ m.
  move=> m; rewrite Poly.varE Poly.car_mono => /SMS.elem_of_singleton ->.
  by move=> /MSet.elem_of_singleton; apply: hash_nonce.
have hS : ∀ m, m ∈ Poly.car sp → y ∉ m.
  move=> m /car_scalar [->|->].
  - by move=> /MSet.elem_of_singleton; apply: hash_nonce.
  - case/MSet.elem_of_disj_union => /MSet.elem_of_singleton e.
    + exact: yum e.
    + exact: hash_nonce e.
have [Dfree [Lin _]] := lin_parts hA hQ hS er.
set D := Frac.den r in Dfree Lin.
have nD : D ≠ Poly.zero := Frac.den_neq0 r.
have xm : ux ≠ um.
  by move=> e; exact: (hash_nonce x_a t_a X_a (TExp g p_b) (eq_sym e)).
have pm : up ≠ um.
  by move=> e; exact: (hash_nonce p_a t_a X_a (TExp g p_b) (eq_sym e)).
have nsp : sp ≠ Poly.zero.
  move=> e; apply: (@coeff_scalar ux um up {[+ ux +]} xm (or_introl eq_refl)).
  by rewrite -/sp e Poly.coeff_zero.
have nSD : (sp * D)%P ≠ Poly.zero := PolyGcd.mul_neq0 _ _ nsp nD.
(* A monomial of [sp⋅D] with the most occurrences of [a]. *)
have [ρ' [cρ' dρ']] := PolyGcd.deg_witness ua (sp * D)%P nSD.
have ρ'SD := proj1 (Poly.coeff_neq0_elem _ _) cρ'.
have dsp : 1 ≤ Poly.deg ua sp.
  case: ha => ea.
  - have := PolyGcd.count_le_deg ua {[+ ux +]} sp
              (@coeff_scalar ux um up _ xm (or_introl eq_refl)).
    by rewrite /ua ea MSet.count_singleton bool_decide_eq_true_2.
  - have := PolyGcd.count_le_deg ua ({[+ um +]} ⊎ {[+ up +]}) sp
              (@coeff_scalar ux um up _ xm (or_intror eq_refl)).
    rewrite /ua ea MSet.count_disj_union !MSet.count_singleton.
    by rewrite bool_decide_eq_false_2 ?bool_decide_eq_true_2.
set ν := {[+ y +]} ⊎ ({[+ ub +]} ⊎ ρ').
have νN : ν ∈ Poly.car (Frac.num r).
  apply: Lin; rewrite Poly.varE Poly.car_mul_mono; apply/SMS.elem_of_count.
  rewrite (SMS.count_map_inj (λ n, {[+ ub +]} ⊎ n)).
  - exact/SMS.elem_of_count.
  - move=> m1 m2 e; apply: MSet.count_inj => z.
    by move/(f_equal (MSet.count z)): e; rewrite !MSet.count_disj_union; lia.
have [u [uK G]] := gfactors_of_log νN.
exists u; split; first exact: uK.
have ca := count_expo_gfactor G (y := TNonce a) I.
have cb := count_expo_gfactor G (y := TNonce p_b) I.
rewrite -/r -/D -/ua in ca; rewrite -/r -/D -/ub in cb.
have cy z : z ≠ y → MSet.count z ν = MSet.count z ({[+ ub +]} ⊎ ρ').
  move=> zy; rewrite /ν MSet.count_disj_union MSet.count_singleton.
  by rewrite bool_decide_eq_false_2.
have ya : ua ≠ y.
  by move=> e; exact: (hash_nonce a t_b X_b P_a (eq_sym e)).
have yb : ub ≠ y.
  by move=> e; exact: (hash_nonce p_b t_b X_b P_a (eq_sym e)).
have Dle := PolyGcd.content_le_deg ua _ nD.
have dSD := PolyGcd.deg_mul ua _ _ nsp nD.
have cSD := proj1 (MSet.subseteq_count _ _)
  (PolyGcd.content_sub _ ρ' ρ'SD) ub.
rewrite (PolyGcd.content_mul _ _ nsp nD) MSet.count_disj_union in cSD.
apply: pos_exps_two.
- rewrite ca (cy _ ya) MSet.count_disj_union MSet.count_singleton.
  case: (bool_decide_reflect (TNonce a = TNonce p_b)) => [e|ne].
    rewrite bool_decide_eq_true_2; last by rewrite /ua /ub e.
    lia.
  rewrite bool_decide_eq_false_2; last by move=> /unfold_term_inj.
  lia.
- rewrite cb (cy _ yb) MSet.count_disj_union MSet.count_singleton.
  rewrite bool_decide_eq_true_2 //; lia.
Qed.

Lemma hmqv_K_gfactor_mixed t_a t_b (p_a x_a p_b : nonce) P_a X_a X_b :
  negb (is_exp g) → negb (is_gmul g) → t_a ≠ t_b →
  ∃ u, u ∈ gfactors (hmqv_K t_a t_b p_a x_a P_a X_a (TExp g p_b) X_b) ∧
       {[+ TNonce x_a; TNonce p_b +]} ⊆ SMS.pos (exps u).
Proof. by move=> gNX gNm tab; apply: hmqv_K_gfactor_peer => //; left. Qed.

Lemma hmqv_K_gfactor_static t_a t_b (p_a x_a p_b : nonce) P_a X_a X_b :
  negb (is_exp g) → negb (is_gmul g) → t_a ≠ t_b →
  ∃ u, u ∈ gfactors (hmqv_K t_a t_b p_a x_a P_a X_a (TExp g p_b) X_b) ∧
       {[+ TNonce p_a; TNonce p_b +]} ⊆ SMS.pos (exps u).
Proof. by move=> gNX gNm tab; apply: hmqv_K_gfactor_peer => //; right. Qed.

(** With honest shares, the logarithm of the key at [g] is a polynomial, and
    its monomial [x_b⋅x_a] survives. *)
Lemma hmqv_K_gfactor_eph t_a t_b (p_a x_a p_b x_b : nonce) P_a X_a :
  negb (is_exp g) → negb (is_gmul g) →
  ∃ u, u ∈ gfactors (hmqv_K t_a t_b p_a x_a P_a X_a (TExp g p_b)
                            (TExp g x_b)) ∧
       {[+ TNonce x_a; TNonce x_b +]} ⊆ SMS.pos (exps u).
Proof.
move=> gNX gNm.
set K := hmqv_K t_a t_b p_a x_a P_a X_a (TExp g p_b) (TExp g x_b).
set mA := hmqv_m t_a X_a (TExp g p_b).
set mB := hmqv_m t_b (TExp g x_b) P_a.
set y := unfold_term mB.
set ux := unfold_term (TNonce x_a); set up := unfold_term (TNonce p_a).
set ub := unfold_term (TNonce p_b); set uxb := unfold_term (TNonce x_b).
set um := unfold_term mA.
set sp := (Poly.var ux + Poly.var um * Poly.var up)%P.
set r := dh_map K !!! unfold_term g.
have hash_nonce (n : nonce) t X P : unfold_term (hmqv_m t X P) ≠
                                    unfold_term (TNonce n).
  by move/unfold_term_inj.
have er : r = Frac.of_poly
                ((Poly.var uxb + Poly.var ub * Poly.var y) * sp)%P.
  rewrite /r -pre_frac_log /K log_hmqv_K log_hmqv_Y !log_TExp_g //.
  rewrite pre_frac_TMul2 pre_frac_TSum2 pre_frac_TMul2 /hmqv_s pre_frac_TSum2
    pre_frac_TMul2.
  rewrite (pre_frac_atom (a := TNonce x_b)) // (pre_frac_atom (a := TNonce p_b))
    //.
  rewrite (pre_frac_atom (a := mB)); last exact: hmqv_m_Nmod.
  rewrite (pre_frac_atom (a := TNonce x_a)) // (pre_frac_atom (a := TNonce p_a))
    //.
  rewrite (pre_frac_atom (a := mA)); last exact: hmqv_m_Nmod.
  by rewrite /sp !Frac.of_poly_mul !Frac.of_poly_add !Frac.of_poly_mul.
pose (ν := ({[+ uxb +]} ⊎ {[+ ux +]} : MSet.mset PreTerm.pre_term)).
have uxm : ux ≠ um.
  by move=> e; exact: (hash_nonce x_a t_a X_a (TExp g p_b) (eq_sym e)).
assert (νN : ν ∈ Poly.car (Frac.num r)).
  rewrite er Frac.num_of_poly; apply/Poly.coeff_neq0_elem.
  have -> : ((Poly.var uxb + Poly.var ub * Poly.var y) * sp)%P =
            (Poly.mul (Poly.mono {[+ uxb +]}) sp +
             Poly.mul (Poly.mono ({[+ ub +]} ⊎ {[+ y +]})) sp)%P.
    by rewrite !Poly.varE -Poly.mul_mono; ring.
  rewrite Poly.coeff_add Poly.coeff_mono_mul_in
    (Poly.coeff_mono_mul_out _ ν _ y).
  - by rewrite Z.add_0_r; apply: coeff_scalar => //; left.
  - by apply/MSet.elem_of_disj_union; right; apply/MSet.elem_of_singleton.
  - case/MSet.elem_of_disj_union => /MSet.elem_of_singleton e.
    + exact: (hash_nonce x_b t_b (TExp g x_b) P_a e).
    + exact: (hash_nonce x_a t_b (TExp g x_b) P_a e).
have [u [uK G]] := gfactors_of_log νN.
exists u; split; first exact: uK.
have c0 z : MSet.count z (PolyGcd.content (Frac.den r)) = 0.
  rewrite er Frac.den_of_poly Poly.oneE PolyGcd.content_mono.
  exact: MSet.count_empty.
have ca := count_expo_gfactor G (y := TNonce x_a) I.
have cb := count_expo_gfactor G (y := TNonce x_b) I.
rewrite -/r c0 /ν MSet.count_disj_union !MSet.count_singleton -/ux in ca.
rewrite -/r c0 /ν MSet.count_disj_union !MSet.count_singleton -/uxb in cb.
have exb : bool_decide (ux = uxb) = bool_decide (TNonce x_a = TNonce x_b).
  apply: bool_decide_ext; split=> [/unfold_term_inj //|e].
  by rewrite /ux /uxb e.
rewrite (bool_decide_eq_true_2 (ux = ux)) // exb in ca.
rewrite (bool_decide_eq_true_2 (uxb = uxb)) // in cb.
apply: pos_exps_two; rewrite ?ca ?cb; case: bool_decide => /=; lia.
Qed.

End HMQV.

Section HMQVIris.

Context `{!cryptisGS Σ, !heapGS Σ}.
Abbreviation iProp := (iProp Σ).

Implicit Types t : term.

#[local] Lemma minted_hmqv_m N (t : string) X P :
  minted X -∗ minted P -∗ minted (hmqv_m N t X P).
Proof.
iIntros "#mX #mP"; rewrite /hmqv_m.
iApply minted_THash; iApply minted_tag; iApply minted_of_list => /=.
by do !iSplit => //.
Qed.

#[local] Lemma public_hmqv_m N (t : string) X P :
  public X -∗ public P -∗ public (hmqv_m N t X P).
Proof.
iIntros "#pX #pP"; rewrite /hmqv_m.
iApply public_THash; iLeft; iApply public_tag; iApply public_of_list => /=.
by do !iSplit => //.
Qed.

Lemma minted_hmqv_K N t_a t_b p_a x_a P_a X_a P_b X_b :
  minted p_a -∗ minted x_a -∗ minted P_a -∗ minted X_a -∗
  minted P_b -∗ minted X_b -∗
  minted (hmqv_K N t_a t_b p_a x_a P_a X_a P_b X_b).
Proof.
iIntros "#mp #mx #mP #mX #mP' #mX'".
iAssert (minted (hmqv_m N t_a X_a P_b)) as "#mma".
  by iApply minted_hmqv_m.
iAssert (minted (hmqv_m N t_b X_b P_a)) as "#mmb".
  by iApply minted_hmqv_m.
iAssert (minted (hmqv_Y N t_b P_a P_b X_b)) as "#mY".
  rewrite /hmqv_Y; iApply all_minted_TGMul2.
  by do !iSplit => //; iApply all_minted_TExp; iSplit.
rewrite /hmqv_K /hmqv_s; iApply all_minted_TExp; iSplit => //.
iApply all_minted_TSum2; iSplit => //.
by iApply all_minted_TMul2; iSplit.
Qed.

(** Whoever knows all the inputs of the key formula can compute the key. *)

Lemma public_hmqv_K N t_a t_b p_a x_a P_a X_a P_b X_b :
  public p_a -∗ public x_a -∗ public P_a -∗ public X_a -∗
  public P_b -∗ public X_b -∗
  public (hmqv_K N t_a t_b p_a x_a P_a X_a P_b X_b).
Proof.
iIntros "#pp #px #pP #pX #pP' #pX'".
iAssert (public (hmqv_m N t_a X_a P_b)) as "#pma".
  by iApply public_hmqv_m.
iAssert (public (hmqv_m N t_b X_b P_a)) as "#pmb".
  by iApply public_hmqv_m.
iAssert (public (hmqv_Y N t_b P_a P_b X_b)) as "#pY".
  rewrite /hmqv_Y; iApply public_TGMul2 => //.
  by iApply public_TExp.
rewrite /hmqv_K /hmqv_s; iApply public_TExp => //.
iApply public_TSum2 => //.
by iApply public_TMul2.
Qed.

(** The persistent part of a Diffie-Hellman private key, long-term or
    ephemeral: its [exp_pred] lets it be used as a DH exponent.  Whether
    it stays secret is up to its owner. *)

Definition hmqv_key (x : nonce) : iProp :=
  minted x ∗ □ (∀ t, exp_pred x t ↔ ▷ □ dh_key_share t).

#[global] Instance hmqv_key_persistent (x : nonce) : Persistent (hmqv_key x).
Proof. apply _. Qed.

Definition ephemeral (x : nonce) : iProp :=
  hmqv_key x ∗ □ (public x ↔ ▷ False).

#[global] Instance ephemeral_persistent (x : nonce) :
  Persistent (ephemeral x).
Proof. apply _. Qed.

(** With an honest peer share, the ephemeral-ephemeral factor binds the key to
    the two ephemeral private keys. *)

Lemma public_hmqv_K_eph N g t_a t_b (p_a x_a p_b x_b : nonce) P_a X_a :
  negb (is_exp g) → negb (is_gmul g) →
  hmqv_key x_a -∗
  hmqv_key x_b -∗
  public (hmqv_K N t_a t_b p_a x_a P_a X_a (TExp g p_b) (TExp g x_b)) -∗
  public x_a ∨ public x_b.
Proof.
move=> gNX gNm; iIntros "#[_ e_a] #[_ e_b] #p_K".
have [u [uK sub]] :=
  @hmqv_K_gfactor_eph N g t_a t_b p_a x_a p_b x_b P_a X_a gNX gNm.
iEval (rewrite public_gfactors) in "p_K".
iDestruct "p_K" as "[_ #fs]".
iApply (public_dh_secret_gen2 sub with "e_a e_b").
by iApply (big_sepL_elem_of with "fs"); apply/SMS.elem_of_elements.
Qed.

(** A key exchanged between an arbitrary pair of parties with well-formed
    long-term keys is public only if one of the long-term keys was corrupted. *)

Lemma public_hmqv_K_static N g t_a t_b (p_a x_a p_b : nonce) P_a X_a X_b :
  negb (is_exp g) → negb (is_gmul g) →
  t_a ≠ t_b →
  hmqv_key p_a -∗
  hmqv_key p_b -∗
  public (hmqv_K N t_a t_b p_a x_a P_a X_a (TExp g p_b) X_b) -∗
  public p_a ∨ public p_b.
Proof.
move=> gNX gNm tab.
have [u [uK ab_ss]] :=
  @hmqv_K_gfactor_static N g t_a t_b p_a x_a p_b P_a X_a X_b gNX gNm tab.
iIntros "#[_ pred_a] #[_ pred_b] #p_K".
iEval (rewrite public_gfactors) in "p_K".
iDestruct "p_K" as "[_ #fs]".
iApply (public_dh_secret_gen2 ab_ss with "pred_a pred_b").
by iApply (big_sepL_elem_of with "fs"); apply/SMS.elem_of_elements.
Qed.

(** Whatever the peer's share, the mixed factor binds the key to a party's
    ephemeral key and to its peer's long-term key. *)

Lemma public_hmqv_K_mixed N g t_a t_b (p_a x_a p_b : nonce) P_a X_a X_b :
  negb (is_exp g) → negb (is_gmul g) →
  t_a ≠ t_b →
  hmqv_key x_a -∗
  hmqv_key p_b -∗
  public (hmqv_K N t_a t_b p_a x_a P_a X_a (TExp g p_b) X_b) -∗
  public x_a ∨ public p_b.
Proof.
move=> gNX gNm tab.
have [u [uK ab_mixed]] :=
  @hmqv_K_gfactor_mixed N g t_a t_b p_a x_a p_b P_a X_a X_b gNX gNm tab.
iIntros "#[_ pred_x] #[_ pred_p] #p_K".
iEval (rewrite public_gfactors) in "p_K".
iDestruct "p_K" as "[_ #fs]".
iApply (public_dh_secret_gen2 ab_mixed with "pred_x pred_p").
by iApply (big_sepL_elem_of with "fs"); apply/SMS.elem_of_elements.
Qed.

Lemma public_hmqv_K_forged N g t_a t_b (p_a x_a p_b : nonce) P_a X_a X_b :
  negb (is_exp g) → negb (is_gmul g) →
  t_a ≠ t_b →
  hmqv_key p_a -∗
  hmqv_key x_a -∗
  hmqv_key p_b -∗
  public (hmqv_K N t_a t_b p_a x_a P_a X_a (TExp g p_b) X_b) -∗
  public p_b ∨ public p_a ∗ public x_a.
Proof.
move=> gNX gNm tab.
iIntros "#key_pa #key_xa #key_pb #p_K".
iDestruct (@public_hmqv_K_static N g t_a t_b p_a x_a p_b P_a X_a X_b
             gNX gNm tab with "key_pa key_pb p_K") as "[p_pa|p_pb]";
  last by iLeft.
iDestruct (@public_hmqv_K_mixed N g t_a t_b p_a x_a p_b P_a X_a X_b
             gNX gNm tab with "key_xa key_pb p_K") as "[p_xa|p_pb]";
  last by iLeft.
iRight. by iSplit.
Qed.

Lemma public_hmqv_K_honest N g t_a t_b (p_a x_a p_b x_b : nonce) :
  negb (is_exp g) → negb (is_gmul g) →
  t_a ≠ t_b →
  hmqv_key p_a -∗
  hmqv_key x_a -∗
  hmqv_key p_b -∗
  hmqv_key x_b -∗
  public (hmqv_K N t_a t_b p_a x_a (TExp g p_a) (TExp g x_a)
                 (TExp g p_b) (TExp g x_b)) -∗
  public p_a ∗ public x_a ∨ public p_b ∗ public x_b.
Proof.
move=> gNX gNm tab.
have tba : t_b ≠ t_a by congruence.
iIntros "#key_pa #key_xa #key_pb #key_xb #p_K".
iDestruct (@public_hmqv_K_static N g t_a t_b p_a x_a p_b
             (TExp g p_a) (TExp g x_a) (TExp g x_b) gNX gNm tab
             with "key_pa key_pb p_K") as "#S".
iDestruct (@public_hmqv_K_eph N g t_a t_b p_a x_a p_b x_b
             (TExp g p_a) (TExp g x_a) gNX gNm
             with "key_xa key_xb p_K") as "#E".
iDestruct (@public_hmqv_K_mixed N g t_a t_b p_a x_a p_b
             (TExp g p_a) (TExp g x_a) (TExp g x_b) gNX gNm tab
             with "key_xa key_pb p_K") as "#M1".
iEval (rewrite hmqv_K_sym) in "p_K".
iDestruct (@public_hmqv_K_mixed N g t_b t_a p_b x_b p_a
             (TExp g p_b) (TExp g x_b) (TExp g x_a) gNX gNm tba
             with "key_xb key_pa p_K") as "#M2".
iDestruct "S" as "[?|?]".
- iDestruct "M1" as "[?|?]"; first by iLeft; iSplit.
  iDestruct "E" as "[?|?]"; [iLeft|iRight]; by iSplit.
- iDestruct "M2" as "[?|?]"; first by iRight; iSplit.
  iDestruct "E" as "[?|?]"; [iLeft|iRight]; by iSplit.
Qed.

Definition hmqv_ke N (t_a t_b : string) : val :=
  λ: "p_a" "x_a" "P_a" "X_a" "P_b" "X_b",
  let: "m_a" := hash (tag (Tag $ N.@t_a) (term_of_list ["X_a"; "P_b"])) in
  let: "m_b" := hash (tag (Tag $ N.@t_b) (term_of_list ["X_b"; "P_a"])) in
  let: "Y" := tgmul "X_b" (texp "P_b" "m_b") in
  texp "Y" (tadd "x_a" (tmul "m_a" "p_a")).

Lemma wp_hmqv_ke N t_a t_b (p_a x_a P_a X_a P_b X_b : term) Ψ :
  Ψ (repr (hmqv_K N t_a t_b p_a x_a P_a X_a P_b X_b)) ⊢
  WP hmqv_ke N t_a t_b p_a x_a P_a X_a P_b X_b {{ Ψ }}.
Proof.
rewrite /hmqv_K /hmqv_s; iIntros "post".
wp_lam; wp_pures.
wp_list; wp_apply wp_term_of_list; wp_apply wp_tag; wp_apply wp_hash; wp_pures.
wp_list; wp_apply wp_term_of_list; wp_apply wp_tag; wp_apply wp_hash; wp_pures.
wp_apply wp_texp.
wp_apply wp_tgmul.
wp_pures.
wp_apply wp_tmul.
wp_apply wp_tadd.
by wp_apply wp_texp.
Qed.

End HMQVIris.
