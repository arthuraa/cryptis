From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis.lib Require Import dh list_sort eexp.

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
    Cryptis currently does not support addition, so we compute [K] using the
    equivalent formula:

        K   = (Y_j^x_i) (Y_j^(m_i ⋅ p_i))
            = (Y_i^x_j) (Y_i^(m_j ⋅ p_j))
        Y_i = X_i P_i^m_i
        Y_j = X_j P_j^m_j,

    which only requires multiplication and exponentiation in the Diffie-Hellman
    group and exponent multiplication.  Though this is less efficient than the
    original formula, which requires two exponentiation operations, it offers
    the same security guarantees.


    [hmqv_K t_a t_b p_a x_a P_a X_a P_b X_b] computes the key formula from the
    tags, a party's private keys [p_a] and [x_a], its own public keys [P_a] and
    [X_a] and the peer's public keys [P_b] and [X_b].  The multipliers are
    [hmqv_m t X P = H(t, X, P)].  We prove the following properties:

    - [hmqv_K_sym]: [hmqv_K] produces the same key for the two parties.  This
      property allows them to agree on a shared session key.

    - [hmqv_K_inj] and [hmqv_K_inj']: the session key [K] uniquely determines
      which long-term and ephemeral keys were used, for two keys of the same
      role and for an initiator's and a responder's key, respectively.  The
      long-term keys that the parties accepted for their peers need not be
      vetted, but neither they nor [K] may be the group identity; a vetted
      long-term key is not, and neither is a key computed with it
      ([hmqv_K_neq_unit]).  If the agents' long-term keys represent their
      identity, this means that the key binds who participated in the key
      exchange, an authentication guarantee.  Moreover, if ephemeral keys are
      used only once, this guarantees that session keys are fresh.

    - [hmqv_K_inj_fresh]: the crossed binding for a responder that accepted
      whatever long-term key its peer claimed, the identity included, provided
      that its ephemeral private key is fresh.

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

*)

Section HMQV.

Variable N : namespace.
Variable g : term.

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

#[local] Lemma hmqv_m_Nmul t X P : negb (is_mul (hmqv_m t X P)).
Proof. by rewrite /hmqv_m. Qed.

Definition hmqv_Y (t_b : string) (P_a P_b X_b : term) : term :=
  TGMul {[+ X_b; TExp P_b (hmqv_m t_b X_b P_a) +]}.

Definition hmqv_K (t_a t_b : string) (p_a x_a P_a X_a P_b X_b : term) : term :=
  TGMul {[+ TExp (hmqv_Y t_b P_a P_b X_b) x_a;
            TExp (hmqv_Y t_b P_a P_b X_b) (TMul {[+ hmqv_m t_a X_a P_b; p_a +]})
         +]}.

(** The largest factor of the HMQV key, measured in the number of exponents. *)

#[local] Definition hmqv_ss (t_a t_b : string) (p_a P_a X_a p_b X_b : term) :
  term :=
  TExp g (TMul {[+ p_b; hmqv_m t_b X_b P_a; hmqv_m t_a X_a (TExp g p_b);
                   p_a +]}).

#[local] Lemma count_hmqv_m_nonce t X P (n : nonce) :
  count (hmqv_m t X P) (TNonce n) = 0%Z.
Proof. by apply: count_atom_ne => //; rewrite /hmqv_m. Qed.

#[local] Lemma count_hmqv_m_e h t X P (p : nonce) :
  count (hmqv_m t X P) (TMul {[+ h; TNonce p +]}) =
  count (hmqv_m t X P) h.
Proof. by rewrite count_TMul2 count_hmqv_m_nonce; lia. Qed.

#[local] Lemma count_hmqv_m_diag t X P :
  count (hmqv_m t X P) (hmqv_m t X P) = 1%Z.
Proof. by apply: count_atom_diag; exact: hmqv_m_Nmul. Qed.

#[local] Lemma count_hmqv_m_neq t X P t' X' P' :
  hmqv_m t X P ≠ hmqv_m t' X' P' →
  count (hmqv_m t X P) (hmqv_m t' X' P') = 0%Z.
Proof. by move=> ne; apply: count_atom_ne => //; exact: hmqv_m_Nmul. Qed.

(** ** The key in extended exponents

    In the language of [eexp.v], [hmqv_K] raises the base [Y = X_b + m_b⋅P_b]
    ([hmqv_Y]) to the scalar [x_a + m_a⋅p_a] ([hmqv_s]).  Its logarithms are
    thus products: for every base [b],

        log b K = (log b X_b + log b P_b⋅m_b)⋅(x_a + m_a⋅p_a).

    For well-formed peer keys, the base is [g] raised to the scalar
    [x_b + m_b⋅p_b], so the two parties raise [g] to the same product of
    scalars, in different orders ([hmqv_K_sym]). *)

(** The scalar [x + m⋅p]. *)
#[local] Definition hmqv_s (m p x : term) : eexp :=
  {[+ x; TMul {[+ m; p +]} +]}.

#[local] Lemma hmqv_K_epow t_a t_b p_a x_a P_a X_a P_b X_b :
  hmqv_K t_a t_b p_a x_a P_a X_a P_b X_b
  = epow (hmqv_Y t_b P_a P_b X_b) (hmqv_s (hmqv_m t_a X_a P_b) p_a x_a).
Proof. by rewrite /hmqv_s epow2. Qed.

#[local] Lemma hmqv_Y_honest t_b P_a p_b x_b :
  hmqv_Y t_b P_a (TExp g p_b) (TExp g x_b)
  = epow g (hmqv_s (hmqv_m t_b (TExp g x_b) P_a) p_b x_b).
Proof. by rewrite /hmqv_s epow2 /hmqv_Y TExpA (comm (⊎) {[+ p_b +]}). Qed.

Lemma hmqv_K_sym t_a t_b p_a x_a p_b x_b :
  hmqv_K t_a t_b p_a x_a (TExp g p_a) (TExp g x_a) (TExp g p_b) (TExp g x_b)
  = hmqv_K t_b t_a p_b x_b (TExp g p_b) (TExp g x_b) (TExp g p_a) (TExp g x_a).
Proof. by rewrite !hmqv_K_epow !hmqv_Y_honest !epowA emul_comm. Qed.

#[local] Lemma log_hmqv_Y b t_b P_a P_b X_b :
  log b (hmqv_Y t_b P_a P_b X_b)
  = log b X_b ⊎ emul (log b P_b) {[+ hmqv_m t_b X_b P_a +]}.
Proof. by rewrite log_TGMul2 log_TExp. Qed.

#[local] Lemma log_hmqv_K b t_a t_b p_a x_a P_a X_a P_b X_b :
  log b (hmqv_K t_a t_b p_a x_a P_a X_a P_b X_b)
  = emul (log b (hmqv_Y t_b P_a P_b X_b)) (hmqv_s (hmqv_m t_a X_a P_b) p_a x_a).
Proof. by rewrite hmqv_K_epow log_epow. Qed.

#[local] Lemma log_TExp_g e :
  negb (is_exp g) → negb (is_gmul g) → log g (TExp g e) = {[+ e +]}.
Proof. by move=> gNX gNm; rewrite log_TExp_atom // bool_decide_eq_true_2. Qed.

(** *** Degrees in the multipliers *)

#[local] Lemma deg_log_hmqv_m t X P T :
  tsize T < tsize (hmqv_m t X P) →
  ∀ b, deg (hmqv_m t X P) (log b T) ⊑ Some (0, 0)%Z.
Proof. by move=> lt; apply: deg_log_small; lia. Qed.

#[local] Lemma deg_log_TExp_g h b (n : nonce) :
  negb (is_exp g) → negb (is_gmul g) → count h (TNonce n) = 0%Z →
  deg h (log b (TExp g n)) ⊑ Some (0, 0)%Z.
Proof.
move=> gNX gNm hn; rewrite log_TExp_atom //.
by case: (bool_decide (g = b)); rewrite ?deg_singleton ?hn ?deg_empty.
Qed.

(** [x + m⋅p] has the degrees 0 and 1 in [m], and the degree 0 in other
    multipliers. *)
#[local] Lemma deg_hmqv_s t X P (p x : nonce) :
  deg (hmqv_m t X P) (hmqv_s (hmqv_m t X P) p x) = Some (0, 1)%Z.
Proof.
have c0 := count_hmqv_m_nonce t X P x.
have c1 : count (hmqv_m t X P) (TMul {[+ hmqv_m t X P; TNonce p +]}) = 1%Z.
  by rewrite count_hmqv_m_e count_hmqv_m_diag.
rewrite /hmqv_s deg_disj_union_apart !deg_singleton ?c0 ?c1 //.
by move=> ? ? ? ?; rewrite ?deg_singleton ?c0 ?c1 => - [<- <-] [<- <-].
Qed.

#[local] Lemma deg_hmqv_s_ne t X P t' X' P' (p x : nonce) :
  hmqv_m t X P ≠ hmqv_m t' X' P' →
  deg (hmqv_m t X P) (hmqv_s (hmqv_m t' X' P') p x) ⊑ Some (0, 0)%Z.
Proof.
move=> ne; apply: deg_le_disj_union; rewrite deg_singleton.
- by rewrite count_hmqv_m_nonce.
- by rewrite count_hmqv_m_e count_hmqv_m_neq.
Qed.

#[local] Lemma deg_log_hmqv_Y h b t_b P_a P_b X_b :
  deg h (log b X_b) ⊑ Some (0, 0)%Z → deg h (log b P_b) ⊑ Some (0, 0)%Z →
  count h (hmqv_m t_b X_b P_a) = 0%Z →
  deg h (log b (hmqv_Y t_b P_a P_b X_b)) ⊑ Some (0, 0)%Z.
Proof.
move=> hX hP hB; rewrite log_hmqv_Y; apply: deg_le_disj_union hX _.
by apply: (deg_le_emul hP); rewrite deg_singleton hB.
Qed.

(* A key has degree 0 in a multiplier other than its own two if its peer keys
   do. *)
#[local] Lemma deg_log_hmqv_K t X P b t_a t_b (p_a x_a : nonce)
    P_a X_a P_b X_b :
  hmqv_m t X P ≠ hmqv_m t_a X_a P_b → hmqv_m t X P ≠ hmqv_m t_b X_b P_a →
  deg (hmqv_m t X P) (log b X_b) ⊑ Some (0, 0)%Z →
  deg (hmqv_m t X P) (log b P_b) ⊑ Some (0, 0)%Z →
  deg (hmqv_m t X P) (log b (hmqv_K t_a t_b p_a x_a P_a X_a P_b X_b))
    ⊑ Some (0, 0)%Z.
Proof.
move=> nA nB hX hP; rewrite log_hmqv_K.
have hY := deg_log_hmqv_Y hX hP (count_hmqv_m_neq nB).
exact: deg_le_emul hY (deg_hmqv_s_ne _ _ nA).
Qed.

(** ** Group factors of the HMQV key

    The HMQV formula guarantees the secrecy of the exchanged key.  To prove
    this property, we need to reason about which factors of the Diffie-Hellman
    group appear in the formula. *)

#[local] Lemma exps_hmqv_ss t_a t_b (p_a p_b : nonce) P_a X_a X_b :
  negb (is_exp g) → negb (is_gmul g) →
  exps (hmqv_ss t_a t_b p_a P_a X_a p_b X_b)
  = SMS.make
      [TNonce p_b; hmqv_m t_b X_b P_a; hmqv_m t_a X_a (TExp g p_b); TNonce p_a]
      [].
Proof.
move=> gNX gNm; rewrite /hmqv_ss (@exps_TExp_TMul g _ gNX gNm).
  by rewrite !SMS.singleton_make !SMS.disj_union_make.
by move=> u; repeat case/SMS.elem_of_disj_union;
   move=> /SMS.elem_of_singleton ->.
Qed.

#[local] Lemma exps_hmqv_mixed t_b (p_b x_a : nonce) P_a X_b :
  negb (is_exp g) → negb (is_gmul g) →
  exps (TExp g (TMul {[+ TNonce p_b; hmqv_m t_b X_b P_a; TNonce x_a +]}))
  = SMS.make [TNonce p_b; hmqv_m t_b X_b P_a; TNonce x_a] [].
Proof.
move=> gNX gNm; rewrite (@exps_TExp_TMul g _ gNX gNm).
  by rewrite !SMS.singleton_make !SMS.disj_union_make.
by move=> u; repeat case/SMS.elem_of_disj_union;
   move=> /SMS.elem_of_singleton ->.
Qed.

(** Whatever the peer's share [X_b], the HMQV key contains the mixed factor
    [g^(p_b ⋅ m_b ⋅ x_a)] and the static-static factor
    [g^(p_b ⋅ m_b ⋅ m_a ⋅ p_a)]: their exponents make up the part of degree 1
    in [m_b] of its logarithm, which [X_b] is too small to cancel. *)

#[local] Lemma TMul3 a b c :
  TMul {[+ a; b; c +]} = TMul {[+ TMul {[+ a; b +]}; c +]}.
Proof.
by apply: count_inj => z _; rewrite !(count_TMul_disj_union, TMul_singleton).
Qed.

#[local] Lemma TMul4 a b c d :
  TMul {[+ a; b; c; d +]} = TMul {[+ TMul {[+ a; b +]}; TMul {[+ c; d +]} +]}.
Proof.
apply: count_inj => z _; rewrite !(count_TMul_disj_union, TMul_singleton).
lia.
Qed.

#[local] Lemma count_log_hmqv_K t_a t_b (p_a x_a p_b : nonce) P_a X_a X_b e :
  negb (is_exp g) → negb (is_gmul g) → t_a ≠ t_b →
  count (hmqv_m t_b X_b P_a) e = 1%Z →
  SMS.count e (log g (hmqv_K t_a t_b p_a x_a P_a X_a (TExp g p_b) X_b))
  = SMS.count e
      {[+ TMul {[+ TNonce p_b; hmqv_m t_b X_b P_a; TNonce x_a +]};
          TMul {[+ TNonce p_b; hmqv_m t_b X_b P_a; hmqv_m t_a X_a (TExp g p_b);
                   TNonce p_a +]} +]}.
Proof.
move=> gNX gNm tab ce.
have nBA : hmqv_m t_b X_b P_a ≠ hmqv_m t_a X_a (TExp g p_b).
  by case/hmqv_m_inj => e' _; apply: tab; rewrite e'.
have z : SMS.count e (emul (log g X_b)
           (hmqv_s (hmqv_m t_a X_a (TExp g p_b)) p_a x_a)) = 0%Z.
  have hX := deg_log_hmqv_m (tsize_hmqv_m_lt t_b X_b P_a) g.
  apply: (deg_count (deg_le_emul hX (deg_hmqv_s_ne p_a x_a nBA))).
  by rewrite ce; lia.
rewrite log_hmqv_K log_hmqv_Y log_TExp_g // emul_singleton emul_disj_union_l.
rewrite SMS.count_disj_union z Z.add_0_l /hmqv_s emul_disj_union_r.
by rewrite !emul_singleton TMul3 TMul4.
Qed.

#[local] Lemma hmqv_K_gfactor t_a t_b (p_a x_a p_b : nonce) P_a X_a X_b s :
  negb (is_exp g) → negb (is_gmul g) →
  let m_a := hmqv_m t_a X_a (TExp g p_b) in
  let m_b := hmqv_m t_b X_b P_a in
  t_a ≠ t_b →
  s = TMul {[+ TNonce p_b; m_b; TNonce x_a +]} ∨
  s = TMul {[+ TNonce p_b; m_b; m_a; TNonce p_a +]} →
  TExp g s
    ∈ SMS.pos (gfactors (hmqv_K t_a t_b p_a x_a P_a X_a (TExp g p_b) X_b)).
Proof.
move=> gNX gNm /= tab Hs.
have nba : hmqv_m t_b X_b P_a ≠ hmqv_m t_a X_a (TExp g p_b).
  by case/hmqv_m_inj => e _; apply: tab; rewrite e.
have ne : TMul {[+ TNonce p_b; hmqv_m t_b X_b P_a; TNonce x_a +]}
          ≠ TMul {[+ TNonce p_b; hmqv_m t_b X_b P_a;
                     hmqv_m t_a X_a (TExp g p_b); TNonce p_a +]}.
  move=> /(f_equal (count (hmqv_m t_a X_a (TExp g p_b)))).
  rewrite !(count_TMul_disj_union, TMul_singleton) count_hmqv_m_diag.
  by rewrite !count_hmqv_m_nonce count_hmqv_m_neq //; exact: not_eq_sym nba.
apply/gcount_gt0; rewrite -count_log // count_log_hmqv_K //; last first.
  case: Hs => ->; rewrite !(count_TMul_disj_union, TMul_singleton).
  - by rewrite count_hmqv_m_diag !count_hmqv_m_nonce.
  - by rewrite count_hmqv_m_diag !count_hmqv_m_nonce count_hmqv_m_neq.
rewrite SMS.count_disj_union !SMS.count_singleton.
case: Hs => ->.
- by rewrite bool_decide_eq_true_2 // bool_decide_eq_false_2.
- by rewrite bool_decide_eq_false_2 ?bool_decide_eq_true_2.
Qed.

#[local] Lemma hmqv_key_gfactors t_a t_b (p_a x_a p_b : nonce) P_a X_a X_b :
  negb (is_exp g) → negb (is_gmul g) →
  let m_b := hmqv_m t_b X_b P_a in
  let ss := hmqv_ss t_a t_b p_a P_a X_a p_b X_b in
  let K := hmqv_K t_a t_b p_a x_a P_a X_a (TExp g p_b) X_b in
  t_a ≠ t_b →
  ss ∈ gfactors K
  ∧ TExp g (TMul {[+ TNonce p_b; m_b; TNonce x_a +]}) ∈ gfactors K
  ∧ [TNonce p_a; TNonce p_b] ⊆+ SMS.pos (exps ss).
Proof.
move=> gNX gNm m_b tab; do !split.
- apply: SMS.elem_of_pos.
  rewrite /hmqv_ss; apply: hmqv_K_gfactor => //; by right.
- apply: SMS.elem_of_pos; apply: hmqv_K_gfactor => //; by left.
- rewrite exps_hmqv_ss // SMS.pos_make_nil_r.
  by apply/submseteq_count_mem => x /=; lia.
Qed.

(** With an honest peer share, the ephemeral-ephemeral factor is in the key:
    the logarithm of the key is a sum of four monomials with positive
    coefficients, so none of them cancels.  This guarantees that the session
    key remains secret when the ephemeral private keys are. *)

#[local] Lemma hmqv_K_gfactor_eph t_a t_b (p_a x_a p_b x_b : nonce) P_a X_a :
  negb (is_exp g) → negb (is_gmul g) →
  TExp g (TMul {[+ TNonce x_b; TNonce x_a +]})
    ∈ gfactors (hmqv_K t_a t_b p_a x_a P_a X_a (TExp g p_b) (TExp g x_b)).
Proof.
move=> gNX gNm; apply: SMS.elem_of_pos; apply/gcount_gt0.
rewrite -count_log // log_hmqv_K log_hmqv_Y !log_TExp_g // emul_singleton.
rewrite /hmqv_s !emul_disj_union_l !emul_disj_union_r !emul_singleton.
rewrite !SMS.count_disj_union !SMS.count_singleton bool_decide_eq_true_2 //.
by repeat case: (bool_decide _) => /=; lia.
Qed.

(** If the shared secret [hmqv_K] degenerates to the group identity, then so
    does the base [hmqv_Y] the party exponentiates, whatever the (unvetted)
    peer keys [P_b] and [X_b] were. *)

Lemma hmqv_K_unit t_a t_b p_a x_a P_a X_a P_b X_b :
  hmqv_K t_a t_b p_a x_a P_a X_a P_b X_b = TGMul ∅ →
  hmqv_Y t_b P_a P_b X_b = TGMul ∅.
Proof.
move=> eK; case: (decide (hmqv_Y t_b P_a P_b X_b = TGMul ∅)) => // nY.
by case: (TExp_add_neq_unit nY eK).
Qed.

(** If two peer ephemerals [X_b], [X_b'] yield the same session key against the
    same claimed [P_b], the initiator exponentiated the same base [hmqv_Y]: the
    key determines that base.  (Together with [hmqv_K_unit] for the degenerate
    key, this is the initiator-side injectivity in its own, unvetted peer
    input.) *)

Lemma hmqv_K_inj_base t_a t_b p_a x_a P_a X_a P_b X_b X_b' :
  hmqv_K t_a t_b p_a x_a P_a X_a P_b X_b
  = hmqv_K t_a t_b p_a x_a P_a X_a P_b X_b' →
  hmqv_Y t_b P_a P_b X_b = hmqv_Y t_b P_a P_b X_b'.
Proof. exact: TExp_add_injl. Qed.

#[local] Lemma sigma_swap a b c :
  TGMul {[+ TExp (TGMul {[+ TExp g a; TExp g b +]}) a;
            TExp (TGMul {[+ TExp g a; TExp g b +]}) c +]}
  = TGMul {[+ TExp (TGMul {[+ TExp g a; TExp g c +]}) a;
              TExp (TGMul {[+ TExp g a; TExp g c +]}) b +]}.
Proof. by rewrite -!epow2 !epowA emul_comm. Qed.

(** A non-trivial session key does NOT bind an *unvetted* peer long-term key.
    Take a degenerate [P_b = 1] on one side and, on the other, a reflected
    ephemeral [X_b' = g^x_a] with [P_b'] chosen so the two bases coincide after
    the swap of [sigma_swap].  Then two distinct peer-key pairs produce the same
    key, which is moreover [≠ 1].  So excluding a trivial key does not suffice
    to bind an unvetted peer; the collision uses [P_b = 1], and excluding that
    too recovers injectivity ([hmqv_K_inj]). *)

Lemma hmqv_K_inj_counterexample t_a t_b (p_a x_a : nonce) P_a X_a :
  negb (is_gmul g) →
  let m_a  := hmqv_m t_a X_a (TGMul ∅) in
  let X_b' := TExp g (TNonce x_a) in
  let m_b' := hmqv_m t_b X_b' P_a in
  let P_b' := TExp g (TMul {[+ m_a; TNonce p_a; TInv m_b' +]}) in
  let m_a' := hmqv_m t_a X_a P_b' in
  let X_b  := TGMul {[+ TExp g (TNonce x_a);
                        TExp g (TMul {[+ m_a'; TNonce p_a +]}) +]} in
  hmqv_K t_a t_b p_a x_a P_a X_a (TGMul ∅) X_b
    = hmqv_K t_a t_b p_a x_a P_a X_a P_b' X_b'
  ∧ hmqv_K t_a t_b p_a x_a P_a X_a (TGMul ∅) X_b ≠ TGMul ∅.
Proof.
move=> gNm m_a X_b' m_b' P_b' m_a' X_b.
have HP : TExp P_b' m_b' = TExp g (TMul {[+ m_a; TNonce p_a +]}).
  rewrite /P_b' TExpA; congr TExp.
  apply: count_inj => z _.
  by rewrite !(count_TMul_disj_union, TMul_singleton) count_TInv; lia.
have HY1 : hmqv_Y t_b P_a (TGMul ∅) X_b = X_b.
  by rewrite /hmqv_Y TExp_gunit TGMul_unit_r.
split.
- have HY2 : hmqv_Y t_b P_a P_b' X_b'
           = TGMul {[+ X_b'; TExp g (TMul {[+ m_a; TNonce p_a +]}) +]}.
    by rewrite /hmqv_Y -/m_b' HP.
  rewrite {1}/hmqv_K -/m_a HY1.
  rewrite /hmqv_K -/m_a' HY2.
  exact: sigma_swap.
- move=> /hmqv_K_unit; rewrite HY1.
  exact: TExp_add_neq_unit (Ngmul_neq_unit gNm).
Qed.

(** ** Binding peer keys

    The session key binds both of the peer's public keys, provided that the key
    is not the identity and that neither long-term key is.  Both conditions are
    needed: the key is the identity exactly when its base is ([hmqv_K_unit]),
    and [hmqv_K_inj_counterexample] collides two keys [≠ 1] using [P_b = 1].
    The two keys may come from different initiators: the key binds all four
    public inputs ([hmqv_K_inj_gen]), hence, for well-formed initiator keys, the
    initiator's private keys as well ([hmqv_K_inj]).

    We compare the logarithms of two equal keys: for every base [b],

        (α + β⋅m_b)⋅(x_a + m_a⋅p_a) = (α' + β'⋅m_b')⋅(x_a' + m_a'⋅p_a'),

    where [α = log b X_b], [β = log b P_b], and so on.  A multiplier is bigger
    than the keys it hashes, so their logarithms have degree 0 in it.  We take
    the largest of the multipliers [m_a], [m_a'], [m_b] and [m_b'] and compare
    degrees in it.

    - If it is [m_a] ([hmqv_K_inj_maxA]), every factor on the right but [m_a']
      has degree 0 in [m_a], so the right-hand side has degree 0 unless
      [m_a = m_a'], whereas multiplying by [x_a + m_a⋅p_a], of degrees 0 and
      1, makes the degrees of the left-hand side span more than one integer
      ([hmqv_K_own]).  Once [m_a = m_a'], and thus [β' = β], the parts of
      degree 1 give [(α + β⋅m_b)⋅m_a⋅p_a = (α' + β⋅m_b')⋅m_a⋅p_a'].  Here [α]
      and [α'] have degree 0 in the larger of [m_b] and [m_b'], but [β] need
      not: two different shifts of [β] cannot agree up to terms of degree 0,
      so [m_b = m_b'] ([hmqv_Y_inj]).

    - If it is [m_b] ([hmqv_K_inj_maxB]), the left-hand side has the part
      [β⋅m_b⋅(x_a + m_a⋅p_a)] of degree 1, which the right-hand side lacks
      unless [m_b = m_b'] ([hmqv_K_peer]).  Comparing these parts, and then
      their degrees in the larger of [m_a] and [m_a'], gives [m_a = m_a']. *)

Lemma hmqv_K_neq_unit t_a t_b (p_a x_a p_b : nonce) P_a X_a X_b :
  negb (is_exp g) → negb (is_gmul g) →
  hmqv_K t_a t_b p_a x_a P_a X_a (TExp g p_b) X_b ≠ TGMul ∅.
Proof.
move=> gNX gNm /hmqv_K_unit /(f_equal (log g)).
rewrite log_unit log_hmqv_Y log_TExp_g // emul_singleton.
set e := TMul {[+ TNonce p_b; hmqv_m t_b X_b P_a +]}.
have ce : SMS.count e (log g X_b) = 0%Z.
  apply: (deg_count (deg_log_hmqv_m (tsize_hmqv_m_lt t_b X_b P_a) g)).
  by rewrite /e count_TMul2 count_hmqv_m_nonce count_hmqv_m_diag; lia.
move=> /(f_equal (SMS.count e)).
rewrite SMS.count_disj_union ce SMS.count_singleton SMS.count_empty.
by rewrite bool_decide_eq_true_2.
Qed.

(** If the other key has degree 0 in [m_a], the base vanishes. *)
#[local] Lemma hmqv_K_own t_a t_b (p_a x_a : nonce) P_a X_a P_b X_b K' :
  (∀ b, deg (hmqv_m t_a X_a P_b) (log b K') ⊑ Some (0, 0)%Z) →
  hmqv_K t_a t_b p_a x_a P_a X_a P_b X_b = K' →
  hmqv_K t_a t_b p_a x_a P_a X_a P_b X_b = TGMul ∅.
Proof.
move=> hK' eK.
enough (E : hmqv_Y t_b P_a P_b X_b = TGMul ∅).
  by rewrite hmqv_K_epow E epow_unit.
apply: log_eq0 => b.
apply: (deg_emul_point (k := 0%Z) (deg_hmqv_s t_a X_a P_b p_a x_a)); first lia.
by rewrite -log_hmqv_K eK.
Qed.

(** If the other key has degree 0 in [m_b], [P_b] vanishes. *)
#[local] Lemma hmqv_K_peer t_a t_b (p_a x_a : nonce) P_a X_a P_b X_b K' :
  t_a ≠ t_b →
  (∀ b, deg (hmqv_m t_b X_b P_a) (log b P_b) ⊑ Some (0, 0)%Z) →
  (∀ b, deg (hmqv_m t_b X_b P_a) (log b K') ⊑ Some (0, 0)%Z) →
  hmqv_K t_a t_b p_a x_a P_a X_a P_b X_b = K' → P_b = TGMul ∅.
Proof.
move=> tab hP hK' eK; apply: log_eq0 => b.
have nBA : hmqv_m t_b X_b P_a ≠ hmqv_m t_a X_a P_b.
  by case/hmqv_m_inj => e _; apply: tab; rewrite e.
have hσ := deg_hmqv_s_ne p_a x_a nBA.
have hX := deg_log_hmqv_m (tsize_hmqv_m_lt t_b X_b P_a) b.
have hB : deg (hmqv_m t_b X_b P_a) {[+ hmqv_m t_b X_b P_a +]} ⊑ Some (1, 1)%Z.
  by rewrite deg_singleton count_hmqv_m_diag.
apply: (emul1_eq0 (e := hmqv_m t_b X_b P_a)).
apply: (deg_emul_point (k := 0%Z) (deg_hmqv_s t_a X_a P_b p_a x_a)); first lia.
enough (E : emul (emul (log b P_b) {[+ hmqv_m t_b X_b P_a +]})
              (hmqv_s (hmqv_m t_a X_a P_b) p_a x_a) = ∅).
  by rewrite E deg_empty.
(* The part of degree 1 in [m_b]. *)
apply: (deg_split (h := hmqv_m t_b X_b P_a) (a := 0%Z) (b := 1%Z)
  (s1 := emul (log b X_b) (hmqv_s (hmqv_m t_a X_a P_b) p_a x_a))
  (r1 := log b K')).
- exact: deg_le_emul hX hσ.
- exact: hK'.
- exact: deg_le_emul (deg_le_emul (hP b) hB) hσ.
- by rewrite deg_empty.
- by [].
- by rewrite (right_id ∅ (⊎)) -eK log_hmqv_K log_hmqv_Y emul_disj_union_l.
Qed.

(* Two different shifts of [β = log b P_b] cannot agree up to terms of degree 0
   in the larger multiplier [m_b]. *)
#[local] Lemma hmqv_Y_inj t_a t_b X_a P_b (p_a p_a' : nonce) P_a X_b P_a' X_b' :
  t_a ≠ t_b → P_b ≠ TGMul ∅ →
  tsize (hmqv_m t_b X_b' P_a') ≤ tsize (hmqv_m t_b X_b P_a) →
  (∀ b,
    emul (log b (hmqv_Y t_b P_a P_b X_b))
      {[+ TMul {[+ hmqv_m t_a X_a P_b; TNonce p_a +]} +]}
    = emul (log b (hmqv_Y t_b P_a' P_b X_b'))
        {[+ TMul {[+ hmqv_m t_a X_a P_b; TNonce p_a' +]} +]}) →
  hmqv_m t_b X_b P_a = hmqv_m t_b X_b' P_a'.
Proof.
move=> tab nP le part.
case: (decide (hmqv_m t_b X_b P_a = hmqv_m t_b X_b' P_a')) => // nB.
have nBA X P : hmqv_m t_b X P ≠ hmqv_m t_a X_a P_b.
  by case/hmqv_m_inj => e _; apply: tab; rewrite e.
have hX X P : tsize X < tsize (hmqv_m t_b X P) →
    tsize (hmqv_m t_b X P) ≤ tsize (hmqv_m t_b X_b P_a) →
    ∀ b (p : nonce),
    deg (hmqv_m t_b X_b P_a)
      (emul (log b X) {[+ TMul {[+ hmqv_m t_a X_a P_b; TNonce p +]} +]})
    ⊑ Some (0, 0)%Z.
  move=> lX lB b p.
  have hL : deg (hmqv_m t_b X_b P_a) (log b X) ⊑ Some (0, 0)%Z.
    by apply: deg_log_hmqv_m; lia.
  apply: (deg_le_emul hL).
  by rewrite deg_singleton count_hmqv_m_e count_hmqv_m_neq.
case: nP; apply: log_eq0 => b; move: (part b).
rewrite !log_hmqv_Y !emul_disj_union_l !emul1A => E.
apply: (emul_lead (h := hmqv_m t_b X_b P_a) (k := 0%Z) _ _ _ E).
- by apply: hX; [exact: tsize_hmqv_m_lt|].
- by apply: hX; [exact: tsize_hmqv_m_lt|].
- rewrite !count_TMul2 count_hmqv_m_diag (count_hmqv_m_neq nB).
  rewrite !count_hmqv_m_nonce; lia.
Qed.

#[local] Lemma hmqv_K_inj_maxA t_a t_b (p_a x_a p_a' x_a' : nonce)
    P_a X_a P_b X_b P_a' X_a' P_b' X_b' :
  t_a ≠ t_b → P_b ≠ TGMul ∅ →
  tsize (hmqv_m t_a X_a' P_b') ≤ tsize (hmqv_m t_a X_a P_b) →
  tsize (hmqv_m t_b X_b P_a) ≤ tsize (hmqv_m t_a X_a P_b) →
  tsize (hmqv_m t_b X_b' P_a') ≤ tsize (hmqv_m t_a X_a P_b) →
  hmqv_K t_a t_b p_a x_a P_a X_a P_b X_b ≠ TGMul ∅ →
  hmqv_K t_a t_b p_a x_a P_a X_a P_b X_b
  = hmqv_K t_a t_b p_a' x_a' P_a' X_a' P_b' X_b' →
  P_a = P_a' ∧ X_a = X_a' ∧ P_b = P_b' ∧ X_b = X_b'.
Proof.
move=> tab nP lA' lB lB' nK eK.
have lP' := tsize_hmqv_m_lt2 t_a X_a' P_b'.
have lX  := tsize_hmqv_m_lt t_b X_b P_a.
have lX' := tsize_hmqv_m_lt t_b X_b' P_a'.
have eA : hmqv_m t_a X_a P_b = hmqv_m t_a X_a' P_b'.
  case: (decide (hmqv_m t_a X_a P_b = hmqv_m t_a X_a' P_b')) => // nA.
  case: nK; apply: (hmqv_K_own _ eK) => b.
  apply: deg_log_hmqv_K.
  - exact: nA.
  - by case/hmqv_m_inj.
  - by apply: deg_log_hmqv_m; lia.
  - by apply: deg_log_hmqv_m; lia.
case/hmqv_m_inj: (eA) => _ [eXa eP]; subst X_a' P_b'.
have hY Q Z b :
    tsize (hmqv_m t_b Z Q) ≤ tsize (hmqv_m t_a X_a P_b) →
    deg (hmqv_m t_a X_a P_b) (log b (hmqv_Y t_b Q P_b Z)) ⊑ Some (0, 0)%Z.
  move=> le; apply: deg_log_hmqv_Y.
  - by apply: deg_log_hmqv_m; have := tsize_hmqv_m_lt t_b Z Q; lia.
  - by apply: deg_log_hmqv_m; have := tsize_hmqv_m_lt2 t_a X_a P_b; lia.
  - by apply: count_hmqv_m_neq; case/hmqv_m_inj.
(* The parts of degree 1 in [m_a]. *)
have part b :
    emul (log b (hmqv_Y t_b P_a P_b X_b))
      {[+ TMul {[+ hmqv_m t_a X_a P_b; TNonce p_a +]} +]}
    = emul (log b (hmqv_Y t_b P_a' P_b X_b'))
        {[+ TMul {[+ hmqv_m t_a X_a P_b; TNonce p_a' +]} +]}.
  have c0 (n : nonce) :
      deg (hmqv_m t_a X_a P_b) {[+ TNonce n +]} ⊑ Some (0, 0)%Z.
    by rewrite deg_singleton count_hmqv_m_nonce.
  have c1 (n : nonce) :
      deg (hmqv_m t_a X_a P_b)
        {[+ TMul {[+ hmqv_m t_a X_a P_b; TNonce n +]} +]} ⊑ Some (1, 1)%Z.
    by rewrite deg_singleton count_hmqv_m_e count_hmqv_m_diag.
  apply: (deg_split (h := hmqv_m t_a X_a P_b) (a := 0%Z) (b := 1%Z)
    (s1 := emul (log b (hmqv_Y t_b P_a P_b X_b)) {[+ TNonce x_a +]})
    (r1 := emul (log b (hmqv_Y t_b P_a' P_b X_b')) {[+ TNonce x_a' +]})).
  - exact: deg_le_emul (hY _ _ b lB) (c0 _).
  - exact: deg_le_emul (hY _ _ b lB') (c0 _).
  - exact: deg_le_emul (hY _ _ b lB) (c1 _).
  - exact: deg_le_emul (hY _ _ b lB') (c1 _).
  - by [].
  - move/(f_equal (log b)): eK.
    by rewrite !log_hmqv_K /hmqv_s !emul_disj_union_r.
have [eXb ePa] : X_b = X_b' ∧ P_a = P_a'.
  case: (Nat.le_ge_cases (tsize (hmqv_m t_b X_b' P_a'))
                         (tsize (hmqv_m t_b X_b P_a))) => le.
  - by case/hmqv_m_inj: (hmqv_Y_inj tab nP le part) => _ [-> ->].
  - have part' b := eq_sym (part b).
    by case/hmqv_m_inj: (hmqv_Y_inj tab nP le part') => _ [-> ->].
by subst.
Qed.

#[local] Lemma hmqv_K_inj_maxB t_a t_b (p_a x_a p_a' x_a' : nonce)
    P_a X_a P_b X_b P_a' X_a' P_b' X_b' :
  t_a ≠ t_b → P_b ≠ TGMul ∅ → P_b' ≠ TGMul ∅ →
  tsize (hmqv_m t_a X_a P_b) ≤ tsize (hmqv_m t_b X_b P_a) →
  tsize (hmqv_m t_a X_a' P_b') ≤ tsize (hmqv_m t_b X_b P_a) →
  tsize (hmqv_m t_b X_b' P_a') ≤ tsize (hmqv_m t_b X_b P_a) →
  hmqv_K t_a t_b p_a x_a P_a X_a P_b X_b
  = hmqv_K t_a t_b p_a' x_a' P_a' X_a' P_b' X_b' →
  P_a = P_a' ∧ X_a = X_a' ∧ P_b = P_b' ∧ X_b = X_b'.
Proof.
move=> tab nP nP' lA lA' lB' eK.
have lP  := tsize_hmqv_m_lt2 t_a X_a P_b.
have lP' := tsize_hmqv_m_lt2 t_a X_a' P_b'.
have lX' := tsize_hmqv_m_lt t_b X_b' P_a'.
have nAB X P X' P' : hmqv_m t_a X P ≠ hmqv_m t_b X' P' by case/hmqv_m_inj.
have hP b : deg (hmqv_m t_b X_b P_a) (log b P_b) ⊑ Some (0, 0)%Z.
  by apply: deg_log_hmqv_m; lia.
have hP' b : deg (hmqv_m t_b X_b P_a) (log b P_b') ⊑ Some (0, 0)%Z.
  by apply: deg_log_hmqv_m; lia.
have eB : hmqv_m t_b X_b P_a = hmqv_m t_b X_b' P_a'.
  case: (decide (hmqv_m t_b X_b P_a = hmqv_m t_b X_b' P_a')) => // nB.
  case: nP; apply: (hmqv_K_peer tab hP _ eK) => b.
  apply: deg_log_hmqv_K.
  - exact: not_eq_sym (nAB _ _ _ _).
  - exact: nB.
  - by apply: deg_log_hmqv_m; lia.
  - exact: hP'.
case/hmqv_m_inj: (eB) => _ [eXb ePa]; subst X_b' P_a'.
(* The parts of degree 1 in [m_b]. *)
have part b :
    emul (emul (log b P_b) {[+ hmqv_m t_b X_b P_a +]})
      (hmqv_s (hmqv_m t_a X_a P_b) p_a x_a)
    = emul (emul (log b P_b') {[+ hmqv_m t_b X_b P_a +]})
        (hmqv_s (hmqv_m t_a X_a' P_b') p_a' x_a').
  have hX := deg_log_hmqv_m (tsize_hmqv_m_lt t_b X_b P_a) b.
  have hσ1 := deg_hmqv_s_ne p_a x_a (not_eq_sym (nAB X_a P_b X_b P_a)).
  have hσ2 := deg_hmqv_s_ne p_a' x_a' (not_eq_sym (nAB X_a' P_b' X_b P_a)).
  have hB :
      deg (hmqv_m t_b X_b P_a) {[+ hmqv_m t_b X_b P_a +]} ⊑ Some (1, 1)%Z.
    by rewrite deg_singleton count_hmqv_m_diag.
  apply: (deg_split (h := hmqv_m t_b X_b P_a) (a := 0%Z) (b := 1%Z)
    (s1 := emul (log b X_b) (hmqv_s (hmqv_m t_a X_a P_b) p_a x_a))
    (r1 := emul (log b X_b) (hmqv_s (hmqv_m t_a X_a' P_b') p_a' x_a'))).
  - exact: deg_le_emul hX hσ1.
  - exact: deg_le_emul hX hσ2.
  - exact: deg_le_emul (deg_le_emul (hP b) hB) hσ1.
  - exact: deg_le_emul (deg_le_emul (hP' b) hB) hσ2.
  - by [].
  - move/(f_equal (log b)): eK.
    by rewrite !log_hmqv_K !log_hmqv_Y !emul_disj_union_l.
(* Their degrees in the larger of [m_a] and [m_a']. *)
have key X P X' P' (p x p' x' : nonce) Q Q' :
    hmqv_m t_a X P ≠ hmqv_m t_a X' P' → tsize Q' < tsize (hmqv_m t_a X P) →
    (∀ b, emul (emul (log b Q) {[+ hmqv_m t_b X_b P_a +]})
            (hmqv_s (hmqv_m t_a X P) p x)
          = emul (emul (log b Q') {[+ hmqv_m t_b X_b P_a +]})
              (hmqv_s (hmqv_m t_a X' P') p' x')) →
    Q = TGMul ∅.
  move=> nA lQ' E; apply: log_eq0 => b.
  apply: (emul1_eq0 (e := hmqv_m t_b X_b P_a)).
  apply: (deg_emul_point (k := 0%Z) (deg_hmqv_s t_a X P p x)); first lia.
  have hQ : deg (hmqv_m t_a X P)
      (emul (log b Q') {[+ hmqv_m t_b X_b P_a +]}) ⊑ Some (0, 0)%Z.
    apply: (deg_le_emul (deg_log_hmqv_m lQ' b)).
    by rewrite deg_singleton (count_hmqv_m_neq (nAB _ _ _ _)).
  by rewrite E; exact: deg_le_emul hQ (deg_hmqv_s_ne _ _ nA).
have eA : hmqv_m t_a X_a P_b = hmqv_m t_a X_a' P_b'.
  case: (decide (hmqv_m t_a X_a P_b = hmqv_m t_a X_a' P_b')) => // nA.
  case: (Nat.le_ge_cases (tsize (hmqv_m t_a X_a' P_b'))
                         (tsize (hmqv_m t_a X_a P_b))) => le.
  - case: nP; apply: (key _ _ _ _ p_a x_a p_a' x_a' P_b P_b' nA _ part).
    lia.
  - case: nP'.
    apply: (key _ _ _ _ p_a' x_a' p_a x_a P_b' P_b (not_eq_sym nA)); first lia.
    by move=> b; rewrite part.
by case/hmqv_m_inj: eA => _ [-> ->].
Qed.

#[local] Lemma hmqv_K_inj_gen t_a t_b (p_a x_a p_a' x_a' : nonce)
    P_a X_a P_b X_b P_a' X_a' P_b' X_b' :
  t_a ≠ t_b → P_b ≠ TGMul ∅ → P_b' ≠ TGMul ∅ →
  hmqv_K t_a t_b p_a x_a P_a X_a P_b X_b ≠ TGMul ∅ →
  hmqv_K t_a t_b p_a x_a P_a X_a P_b X_b
  = hmqv_K t_a t_b p_a' x_a' P_a' X_a' P_b' X_b' →
  P_a = P_a' ∧ X_a = X_a' ∧ P_b = P_b' ∧ X_b = X_b'.
Proof.
move=> tab nP nP' nK eK.
have nK' : hmqv_K t_a t_b p_a' x_a' P_a' X_a' P_b' X_b' ≠ TGMul ∅.
  by rewrite -eK.
have sym : P_a' = P_a ∧ X_a' = X_a ∧ P_b' = P_b ∧ X_b' = X_b →
    P_a = P_a' ∧ X_a = X_a' ∧ P_b = P_b' ∧ X_b = X_b'.
  by case=> -> [-> [-> ->]].
set a  := tsize (hmqv_m t_a X_a P_b).
set a' := tsize (hmqv_m t_a X_a' P_b').
set b  := tsize (hmqv_m t_b X_b P_a).
set b' := tsize (hmqv_m t_b X_b' P_a').
have : (a' ≤ a ∧ b ≤ a ∧ b' ≤ a) ∨ (a ≤ a' ∧ b ≤ a' ∧ b' ≤ a') ∨
       (a ≤ b ∧ a' ≤ b ∧ b' ≤ b) ∨ (a ≤ b' ∧ a' ≤ b' ∧ b ≤ b') by lia.
case=> [[h1 [h2 h3]]|[[h1 [h2 h3]]|[[h1 [h2 h3]]|[h1 [h2 h3]]]]].
- exact: hmqv_K_inj_maxA tab nP h1 h2 h3 nK eK.
- exact: sym (hmqv_K_inj_maxA tab nP' h1 h3 h2 nK' (eq_sym eK)).
- exact: hmqv_K_inj_maxB tab nP nP' h1 h2 h3 eK.
- exact: sym (hmqv_K_inj_maxB tab nP' nP h2 h1 h3 (eq_sym eK)).
Qed.

Lemma hmqv_K_inj t_a t_b (p_a x_a p_a' x_a' : nonce)
    P_b X_b P_b' X_b' :
  negb (is_exp g) → negb (is_gmul g) → t_a ≠ t_b →
  P_b ≠ TGMul ∅ → P_b' ≠ TGMul ∅ →
  hmqv_K t_a t_b p_a x_a (TExp g p_a) (TExp g x_a) P_b X_b ≠ TGMul ∅ →
  hmqv_K t_a t_b p_a x_a (TExp g p_a) (TExp g x_a) P_b X_b
  = hmqv_K t_a t_b p_a' x_a' (TExp g p_a') (TExp g x_a') P_b' X_b' →
  p_a = p_a' ∧ x_a = x_a' ∧ P_b = P_b' ∧ X_b = X_b'.
Proof.
move=> gNX gNm tab nP nP' nK eK.
have [ePa [eXa [-> ->]]] := hmqv_K_inj_gen tab nP nP' nK eK.
move/(f_equal expo): ePa; rewrite !expo_TExp_expN //; case=> ->.
by move/(f_equal expo): eXa; rewrite !expo_TExp_expN //; case=> ->.
Qed.

(** ** Identity binding when receiving messages

    Suppose that Alice and Bob are authenticating.  Each party knows that its
    public keys [P] and [X] are of the form [g^p] and [g^x], but it cannot say
    the same about the other party in general.  Thus, if Bob wants to prove some
    message predicate involving the session (e.g., for the HMQV authenticator
    hash), all that it say is that that session key was computed using his
    private keys and Alice's potentially ill-formed public keys.  When Alice
    receives this message, her perspective is the opposite: she knows that the
    session key was computed using her private keys and Bob's potentially
    ill-formed public keys.  The following set of lemmas, culminating in
    [hmqv_K_inj'], allow the parties to agree on their identities.

    The proof compares logarithms, as for [hmqv_K_inj].  The multipliers [m_a]
    and [m_b] of the initiator's key have counterparts [m_a'] and [m_b'] in the
    responder's key, computed with the same tags.  A multiplier that equals its
    counterpart makes the keys it hashes well formed, so their logarithms have
    degree 0 in every other multiplier.  The other key thus has degree 0 in
    the largest multiplier that differs from its counterpart, which forces a
    key to [1]: the initiator's own key if it is [m_a], its claimed peer key
    [P_b] if it is [m_b] ([hmqv_K_cross_max]). *)

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
have honest b (n : nonce) : deg h (log b (TExp g n)) ⊑ Some (0, 0)%Z.
  apply: deg_log_TExp_g gNX gNm _.
  by case: hh => [[-> _]|[-> _]]; exact: count_hmqv_m_nonce.
have fP b : deg h (log b P_b) ⊑ Some (0, 0)%Z.
  case: (hA) => [/hmqv_m_inj [_ [_ ->]]|[lA _]]; first exact: honest.
  apply: deg_log_small _ b.
  by have := tsize_hmqv_m_lt2 t_a (TExp g x_a) P_b; lia.
have fY b : deg h (log b Y_a) ⊑ Some (0, 0)%Z.
  case: (hA) => [/hmqv_m_inj [_ [<- _]]|[_ lA']]; first exact: honest.
  apply: deg_log_small _ b.
  by have := tsize_hmqv_m_lt t_a Y_a (TExp g p_b); lia.
have fQ b : deg h (log b Q_a) ⊑ Some (0, 0)%Z.
  case: (hB) => [/hmqv_m_inj [_ [_ <-]]|[_ lB']]; first exact: honest.
  apply: deg_log_small _ b.
  by have := tsize_hmqv_m_lt2 t_b (TExp g x_b) Q_a; lia.
case: hh => [[eh nA]|[eh nB]]; subst h.
- case: nK; apply: (hmqv_K_own _ eK) => b.
  exact: deg_log_hmqv_K _ _ (tags _ _ _ _) nA (fY b) (fQ b).
- case: nP; apply: (hmqv_K_peer tab fP _ eK) => b.
  exact: deg_log_hmqv_K _ _ nB (not_eq_sym (tags _ _ _ _)) (fY b) (fQ b).
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

(** ** Binding a claimed key by freshness

    [hmqv_K_inj'] binds a responder's key to the long-term key [P] that its
    peer claimed only if [P] is not the identity.  Freshness can replace that
    check.  Suppose the responder's ephemeral private key [x_b'] differs from
    its long-term private key and occurs neither in [P] nor in the share
    [X_a'] it received.  Then an initiator that computes the same key still
    learns that [P] is its own long-term key.

    Freshness plays the role of size: the logarithms of [P] and [X_a'] have
    degree 0 in every atom with the subterm [x_b'] ([deg_log_fresh]).  The
    logarithm of the responder's key is [y⋅x_b' + y⋅m_b'⋅p_b'], where [y] is
    the logarithm of its base, and each summand has a single degree in such
    an atom, other than that of the initiator's static-static monomial
    [μ = p_b⋅m_b⋅m_a⋅p_a]: the second in [m_b'], and the first in [x_b'] or,
    if [x_b'] is one of the initiator's long-term keys [p_a] or [p_b], in the
    multiplier [m_b] or [m_a] that hashes the corresponding public key.  So
    [μ] occurs in the initiator's key but not in the responder's. *)

#[local] Lemma subterm_hmqv_m n t X P :
  subterm n X ∨ subterm n P → subterm n (hmqv_m t X P).
Proof.
move=> sub; apply: STHash; apply: subterm_tag; rewrite [Spec.of_list]unlock /=.
by case: sub => ?; [apply: STPair1|apply: STPair2; apply: STPair1].
Qed.

Lemma hmqv_K_inj_fresh t_a t_b (p_a x_a p_b p_b' x_b' : nonce) X_b P X_a' :
  negb (is_exp g) → negb (is_gmul g) →
  t_a ≠ t_b →
  ¬ subterm (TNonce x_b') P → ¬ subterm (TNonce x_b') X_a' → x_b' ≠ p_b' →
  hmqv_K t_a t_b p_a x_a (TExp g p_a) (TExp g x_a) (TExp g p_b) X_b
  = hmqv_K t_b t_a p_b' x_b' (TExp g p_b') (TExp g x_b') P X_a' →
  P = TExp g p_a ∧ p_b = p_b' ∧ X_b = TExp g x_b' ∧ X_a' = TExp g x_a.
Proof.
move=> gNX gNm tab fr_P fr_Xa ne_x eK.
have gN1 := Ngmul_neq_unit gNm.
suff eP : P = TExp g p_a.
  move: eK; rewrite eP => eK.
  have nP (p : nonce) : TExp g p ≠ TGMul ∅.
    exact: Ngmul_neq_unit (Ngmul_TExp _ _ gNm).
  have [epb [? [_ ?]]] := hmqv_K_inj' gNX gNm tab (nP p_b) (nP p_a)
                            (hmqv_K_neq_unit gNX gNm) eK.
  by move/(TExp_injr gN1): epb => - [] ?; do !split.
case: (decide (hmqv_m t_b X_b (TExp g p_a) = hmqv_m t_b (TExp g x_b') P))
  => [/hmqv_m_inj [_ [_ ->]] //|neb].
exfalso.
have tags X X' Q Q' : hmqv_m t_a X Q ≠ hmqv_m t_b X' Q'.
  by move=> /hmqv_m_inj [] e _; apply: tab.
set m_a  := hmqv_m t_a (TExp g x_a) (TExp g p_b).
set m_b  := hmqv_m t_b X_b (TExp g p_a).
set m_a' := hmqv_m t_a X_a' (TExp g p_b').
set m_b' := hmqv_m t_b (TExp g x_b') P.
have cN h (n : nonce) : h = m_a ∨ h = m_b ∨ h = m_b' → count h (TNonce n) = 0%Z.
  by case=> [->|[->|->]]; exact: count_hmqv_m_nonce.
have caa : count m_a m_a = 1%Z by exact: count_hmqv_m_diag.
have cbb : count m_b m_b = 1%Z by exact: count_hmqv_m_diag.
have cab : count m_a m_b = 0%Z by apply: count_hmqv_m_neq; exact: tags.
have cba : count m_b m_a = 0%Z.
  by apply: count_hmqv_m_neq; exact: not_eq_sym (tags _ _ _ _).
have cb'a : count m_b' m_a = 0%Z.
  by apply: count_hmqv_m_neq; exact: not_eq_sym (tags _ _ _ _).
have cb'b : count m_b' m_b = 0%Z.
  by apply: count_hmqv_m_neq; exact: not_eq_sym neb.
set μ := TMul {[+ TNonce p_b; m_b; m_a; TNonce p_a +]}.
have cμ h : count h μ = (count h (TNonce p_b) + count h m_b + count h m_a
                         + count h (TNonce p_a))%Z.
  by rewrite /μ !(count_TMul_disj_union, TMul_singleton).
(* [μ] occurs once in the initiator's key. *)
have cbμ : count m_b μ = 1%Z by rewrite cμ cbb cba !cN //; auto.
have : SMS.count μ (log g (hmqv_K t_a t_b p_a x_a (TExp g p_a) (TExp g x_a)
                              (TExp g p_b) X_b)) = 1%Z.
  rewrite (count_log_hmqv_K _ _ _ _ gNX gNm tab cbμ) -/m_a -/m_b.
  rewrite SMS.count_disj_union !SMS.count_singleton.
  rewrite bool_decide_eq_false_2 ?bool_decide_eq_true_2 //.
  move=> /(f_equal (count m_a)).
  rewrite cμ !(count_TMul_disj_union, TMul_singleton) caa !cN; auto; lia.
(* The logarithms of the responder's base have degree 0 in every atom with
   the subterm [x_b'] but [m_a']. *)
have hY h : subterm (TNonce x_b') h → h ≠ m_a' →
    deg h (log g (hmqv_Y t_a (TExp g p_b') P X_a')) ⊑ Some (0, 0)%Z.
  move=> x_h n_h; apply: deg_log_hmqv_Y.
  - exact: deg_log_fresh x_h fr_Xa g.
  - exact: deg_log_fresh x_h fr_P g.
  - exact: count_atom_ne (hmqv_m_Nmul _ _ _) n_h.
have [h1 [x_h1 [n_h1 c_h1]]] : ∃ h1, subterm (TNonce x_b') h1 ∧ h1 ≠ m_a' ∧
    count h1 μ ≠ count h1 (TNonce x_b').
  case: (decide (x_b' = p_a)) => [e|ne_a].
    exists m_b; split; [|split].
    - rewrite /m_b -e; apply: subterm_hmqv_m; right; exact: subterm_TExp_g.
    - exact: not_eq_sym (tags _ _ _ _).
    - by rewrite cbμ cN; auto.
  case: (decide (x_b' = p_b)) => [e|ne_b].
    exists m_a; split; [|split].
    - rewrite /m_a -e; apply: subterm_hmqv_m; right; exact: subterm_TExp_g.
    - rewrite /m_a /m_a' => /hmqv_m_inj [_ [_ /(TExp_injr gN1) [e']]].
      by apply: ne_x; rewrite e e'.
    - by rewrite cμ cab caa !cN; auto.
  exists (TNonce x_b'); split; [by []|split; first by rewrite /m_a'].
  have cxn (n : nonce) : x_b' ≠ n → count (TNonce x_b') (TNonce n) = 0%Z.
    by move=> ne; apply: count_atom_ne => // - [] /ne.
  have cxm t X Q : count (TNonce x_b') (hmqv_m t X Q) = 0%Z.
    by apply: count_atom_ne; [exact: hmqv_m_Nmul|rewrite /hmqv_m].
  rewrite cμ (cxn _ ne_b) (cxn _ ne_a) /m_b /m_a !cxm count_atom_diag //.
have x_mb' : subterm (TNonce x_b') m_b'.
  by rewrite /m_b'; apply: subterm_hmqv_m; left; exact: subterm_TExp_g.
have sh h e : deg h {[+ e +]} ⊑ Some (count h e, count h e).
  by rewrite deg_singleton.
have z1 : SMS.count μ (emul (log g (hmqv_Y t_a (TExp g p_b') P X_a'))
                         {[+ TNonce x_b' +]}) = 0%Z.
  by apply: (deg_count (deg_le_emul (hY _ x_h1 n_h1) (sh _ _))); lia.
have z2 : SMS.count μ (emul (log g (hmqv_Y t_a (TExp g p_b') P X_a'))
                         {[+ TMul {[+ m_b'; TNonce p_b' +]} +]}) = 0%Z.
  apply: (deg_count (deg_le_emul (hY _ x_mb' (not_eq_sym (tags _ _ _ _)))
                                 (sh _ _))).
  rewrite count_hmqv_m_e count_hmqv_m_diag cμ cb'b cb'a !cN; auto; lia.
rewrite eK log_hmqv_K /hmqv_s emul_disj_union_r SMS.count_disj_union.
by rewrite z1 z2.
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
iAssert (minted (TMul {[+ hmqv_m N t_a X_a P_b; p_a +]})) as "#mma_pa".
  by iApply all_minted_TMul2; iSplit.
rewrite /hmqv_K; iApply all_minted_TGMul2.
by do !iSplit => //; iApply all_minted_TExp; iSplit.
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
rewrite /hmqv_K; iApply public_TGMul2; iApply public_TExp => //.
by iApply public_TMul2.
Qed.

(** The persistent part of a Diffie-Hellman private key, long-term or
    ephemeral: its [exp_pred] lets it be used as a DH exponent.  Whether
    it stays secret is up to its owner. *)

Definition hmqv_key (x : nonce) : iProp :=
  minted x ∗ □ (∀ t, exp_pred x t ↔ ▷ □ dh_key_share t).

#[global] Instance hmqv_key_persistent (x : nonce) : Persistent (hmqv_key x).
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
have Nm_a : negb (is_mul (TNonce x_a)) by [].
have Nm_b : negb (is_mul (TNonce x_b)) by [].
iEval (rewrite public_gfactors) in "p_K".
iDestruct "p_K" as "[_ #fs]".
iAssert (public (TExp g (TMul {[+ TNonce x_b; TNonce x_a +]}))) as "#p_eph".
  iApply (big_sepL_elem_of with "fs").
  exact: hmqv_K_gfactor_eph.
iDestruct (@public_dh_secret2 _ _ _ g (TNonce x_b) (TNonce x_a)
             gNX gNm Nm_b Nm_a
             with "e_b e_a p_eph") as "[p_x | p_x]"; eauto.
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
have [gf [_ ab_ss]] :=
  @hmqv_key_gfactors N g t_a t_b p_a x_a p_b P_a X_a X_b gNX gNm tab.
iIntros "#[_ pred_a] #[_ pred_b] #p_K".
iEval (rewrite public_gfactors) in "p_K".
iDestruct "p_K" as "[_ #fs]".
iApply (public_dh_secret_gen2 ab_ss with "pred_a pred_b").
by iApply (big_sepL_elem_of with "fs").
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
have [_ [gf _]] :=
  @hmqv_key_gfactors N g t_a t_b p_a x_a p_b P_a X_a X_b gNX gNm tab.
have ab_mixed : [TNonce x_a; TNonce p_b]
    ⊆+ SMS.pos
         (exps (TExp g (TMul {[+ TNonce p_b; hmqv_m N t_b X_b P_a;
                                  TNonce x_a +]}))).
  rewrite exps_hmqv_mixed // SMS.pos_make_nil_r.
  by apply/submseteq_count_mem => x /=; lia.
iIntros "#[_ pred_x] #[_ pred_p] #p_K".
iEval (rewrite public_gfactors) in "p_K".
iDestruct "p_K" as "[_ #fs]".
iApply (public_dh_secret_gen2 ab_mixed with "pred_x pred_p").
by iApply (big_sepL_elem_of with "fs").
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

(** Facts about the private key behind a public key [X = g^x], stated on the
    public key, which is all a session record keeps. *)

Definition exp_public g X : iProp :=
  ∃ x : nonce, ⌜X = TExp g x⌝ ∗ public x.

Definition exp_frozen g X : iProp :=
  ∀ x : nonce, ⌜X = TExp g x⌝ → □ (public x ↔ ▷ False).

#[global] Instance exp_public_persistent g X : Persistent (exp_public g X).
Proof. apply _. Qed.

#[global] Instance exp_frozen_persistent g X : Persistent (exp_frozen g X).
Proof. apply _. Qed.

Lemma exp_frozen_intro g (x : nonce) :
  negb (is_gmul g) →
  □ (public x ↔ ▷ False) -∗ exp_frozen g (TExp g x).
Proof.
move=> gNm; iIntros "#s %x' %e".
by move/(TExp_injr (Ngmul_neq_unit gNm)): e => - [] <-.
Qed.

Lemma exp_frozen_public g X : exp_frozen g X -∗ exp_public g X -∗ ▷ False.
Proof.
iIntros "#frozen (%x & -> & #p_x)".
iDestruct ("frozen" $! x with "[//]") as "#s". by iApply "s".
Qed.

Definition hmqv_ke N (t_a t_b : string) : val :=
  λ: "p_a" "x_a" "P_a" "X_a" "P_b" "X_b",
  let: "m_a" := hash (tag (Tag $ N.@t_a) (term_of_list ["X_a"; "P_b"])) in
  let: "m_b" := hash (tag (Tag $ N.@t_b) (term_of_list ["X_b"; "P_a"])) in
  let: "Y" := tgmul "X_b" (texp "P_b" "m_b") in
  tgmul (texp "Y" "x_a") (texp "Y" (tmul "m_a" "p_a")).

Lemma wp_hmqv_ke N t_a t_b (p_a x_a P_a X_a P_b X_b : term) Ψ :
  Ψ (repr (hmqv_K N t_a t_b p_a x_a P_a X_a P_b X_b)) ⊢
  WP hmqv_ke N t_a t_b p_a x_a P_a X_a P_b X_b {{ Ψ }}.
Proof.
iIntros "post".
wp_lam; wp_pures.
wp_list; wp_apply wp_term_of_list; wp_apply wp_tag; wp_apply wp_hash; wp_pures.
wp_list; wp_apply wp_term_of_list; wp_apply wp_tag; wp_apply wp_hash; wp_pures.
wp_apply wp_texp.
wp_apply wp_tgmul.
wp_pures.
wp_apply wp_tmul.
wp_apply wp_texp.
wp_apply wp_texp.
by wp_apply wp_tgmul.
Qed.

End HMQVIris.
