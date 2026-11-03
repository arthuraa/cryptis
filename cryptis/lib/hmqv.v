From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis.lib Require Import dh list_sort.

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

#[local] Lemma hmqv_K_expand t_a t_b p_a x_a P_a X_a p_b X_b :
  hmqv_K t_a t_b p_a x_a P_a X_a (TExp g p_b) X_b
  = TGMul {[+ TExp X_b x_a;
              TExp g (TMul {[+ p_b; hmqv_m t_b X_b P_a; x_a +]});
              TExp X_b (TMul {[+ hmqv_m t_a X_a (TExp g p_b); p_a +]});
              hmqv_ss t_a t_b p_a P_a X_a p_b X_b +]}.
Proof.
rewrite /hmqv_K /hmqv_Y /hmqv_ss.
set m_a := hmqv_m t_a X_a (TExp g p_b).
set m_b := hmqv_m t_b X_b P_a.
have eB : TExp (TExp (TExp g p_b) m_b) x_a =
          TExp g (TMul {[+ p_b; m_b; x_a +]}).
  rewrite !TExpA; congr TExp; apply: count_inj => z _.
  rewrite !count_TMul_disj_union !TMul_singleton.
  rewrite !count_TMul_disj_union !TMul_singleton; lia.
have eD : TExp (TExp (TExp g p_b) m_b) (TMul {[+ m_a; p_a +]}) =
          TExp g (TMul {[+ p_b; m_b; m_a; p_a +]}).
  rewrite !TExpA; congr TExp; apply: count_inj => z _.
  rewrite !count_TMul_disj_union !TMul_singleton.
  rewrite !count_TMul_disj_union !TMul_singleton.
  rewrite !count_TMul_disj_union !TMul_singleton; lia.
rewrite !TExp_TGMul !SMS.map_disj_union !SMS.map_singleton eB eD.
by rewrite -TGMul_disj_union (assoc (⊎)).
Qed.

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

Lemma hmqv_K_sym t_a t_b p_a x_a p_b x_b :
  hmqv_K t_a t_b p_a x_a (TExp g p_a) (TExp g x_a) (TExp g p_b) (TExp g x_b)
  = hmqv_K t_b t_a p_b x_b (TExp g p_b) (TExp g x_b) (TExp g p_a) (TExp g x_a).
Proof.
rewrite !hmqv_K_expand /hmqv_ss !TExpA.
set m_a := hmqv_m t_a (TExp g x_a) (TExp g p_b).
set m_b := hmqv_m t_b (TExp g x_b) (TExp g p_a).
have scal : ∀ s1 s2, (∀ z, count z (TMul s1) = count z (TMul s2)) →
                     TMul s1 = TMul s2.
  by move=> s1 s2 e; apply: count_inj => z _.
have e1 : TMul {[+ x_b; x_a +]} = TMul {[+ x_a; x_b +]} by rewrite (comm (⊎)).
have e2 : TMul {[+ p_b; m_b; x_a +]} = TMul {[+ x_a; TMul {[+ m_b; p_b +]} +]}.
  apply: scal => z; rewrite !count_TMul_disj_union !TMul_singleton.
  rewrite !count_TMul_disj_union !TMul_singleton; lia.
have e3 : TMul {[+ x_b; TMul {[+ m_a; p_a +]} +]} = TMul {[+ p_a; m_a; x_b +]}.
  apply: scal => z; rewrite !count_TMul_disj_union !TMul_singleton.
  rewrite !count_TMul_disj_union !TMul_singleton; lia.
have e4 : TMul {[+ p_b; m_b; m_a; p_a +]} = TMul {[+ p_a; m_a; m_b; p_b +]}.
  apply: scal => z; rewrite !count_TMul_disj_union !TMul_singleton; lia.
rewrite e1 e2 e3 e4; congr TGMul.
apply: SMS.count_inj => z; rewrite !SMS.count_disj_union !SMS.count_singleton.
lia.
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
    [g^(p_b ⋅ m_b ⋅ m_a ⋅ p_a)]. *)

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
move=> gNX gNm m_a m_b tab Hs.
have mb_ma : m_b ≠ m_a.
  by rewrite /m_a /m_b => /hmqv_m_inj [] e _; apply: tab; congruence.
(* [m_b] is an exponent of the factor, and of nothing [X_b] gets raised to. *)
have mb_s : m_b ∈ exps (TExp g s).
  by case: Hs => ->; [rewrite exps_hmqv_mixed|rewrite exps_hmqv_ss] => //;
     rewrite SMS.elem_of_make_nil_r; set_solver.
have mb_xa : m_b ∉ factors (TNonce x_a) by apply: not_elem_of_factors_atom.
have mb_ma_pa : m_b ∉ factors (TMul {[+ m_a; TNonce p_a +]}).
  apply: not_elem_of_factors_TMul => u.
  by case/SMS.elem_of_disj_union => /SMS.elem_of_singleton ->.
have ltX : tsize X_b < tsize m_b by exact: tsize_hmqv_m_lt.
have z1 : gcount (TExp g s) (TExp X_b (TNonce x_a)) = 0%Z
  := gcount_TExp_eq0 X_b (TNonce x_a) (TExp g s) m_b mb_s mb_xa ltX.
have z3 : gcount (TExp g s) (TExp X_b (TMul {[+ m_a; TNonce p_a +]})) = 0%Z
  := gcount_TExp_eq0 X_b _ (TExp g s) m_b mb_s mb_ma_pa ltX.
apply/gcount_gt0.
rewrite hmqv_K_expand !gcount_TGMul_disj_union !TGMul_singleton /hmqv_ss.
rewrite -/m_a -/m_b z1 z3.
set e3 := TMul {[+ TNonce p_b; m_b; TNonce x_a +]} in Hs *.
set e4 := TMul {[+ TNonce p_b; m_b; m_a; TNonce p_a +]} in Hs *.
have := @gcount_TExp_g_ge0 g gNm e3 e4.
have := @gcount_TExp_g_ge0 g gNm e4 e3.
by case: Hs => ->; rewrite (gcount_TExp_g_diag gNm); lia.
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

(** With an honest peer share, the ephemeral-ephemeral factor is in the key.
    This guarantees that the session key remains secret when the ephemeral
    private keys are. *)

#[local] Lemma hmqv_K_gfactor_eph t_a t_b (p_a x_a p_b x_b : nonce) P_a X_a :
  negb (is_gmul g) →
  TExp g (TMul {[+ TNonce x_b; TNonce x_a +]})
    ∈ gfactors (hmqv_K t_a t_b p_a x_a P_a X_a (TExp g p_b) (TExp g x_b)).
Proof.
move=> gNm.
set m_a := hmqv_m t_a X_a (TExp g p_b).
set m_b := hmqv_m t_b (TExp g x_b) P_a.
apply: SMS.elem_of_pos; apply/gcount_gt0.
rewrite hmqv_K_expand !TExpA !gcount_TGMul_disj_union !TGMul_singleton.
rewrite /hmqv_ss -/m_a -/m_b (gcount_TExp_g_diag gNm).
set e := TMul {[+ TNonce x_b; TNonce x_a +]}.
set e2 := TMul {[+ TNonce p_b; m_b; TNonce x_a +]}.
set e3 := TMul {[+ TNonce x_b; TMul {[+ m_a; TNonce p_a +]} +]}.
set e4 := TMul {[+ TNonce p_b; m_b; m_a; TNonce p_a +]}.
have := @gcount_TExp_g_ge0 g gNm e e2.
have := @gcount_TExp_g_ge0 g gNm e e3.
have := @gcount_TExp_g_ge0 g gNm e e4.
lia.
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
Proof.
rewrite !TExp_TGMul !SMS.map_disj_union !SMS.map_singleton !TExpA.
apply: gcount_inj => z _.
rewrite !(gcount_TGMul_disj_union, TGMul_singleton).
rewrite (comm (⊎) {[+ b +]} {[+ a +]}) (comm (⊎) {[+ c +]} {[+ a +]}).
rewrite (comm (⊎) {[+ c +]} {[+ b +]}); lia.
Qed.

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

    The proof looks at the largest of the four multipliers
    [A = H(t_a, X_a, P_b)], [A' = H(t_a, X_a', P_b')], [B = H(t_b, X_b, P_a)]
    and [B' = H(t_b, X_b', P_a')].  It is bigger than every input of the other
    key, so it occurs in none of them, and counting it in exponents separates
    the two keys unless it equals its counterpart.  One agreeing pair then pins
    down the other: [hmqv_K_inj_Y] when [A = A'], [hmqv_K_inj_X] when
    [B = B']. *)

#[local] Lemma gcount_hmqv_K t t_a t_b p_a x_a P_a X_a P_b X_b :
  gcount t (hmqv_K t_a t_b p_a x_a P_a X_a P_b X_b) =
  (gcount t (TExp (hmqv_Y t_b P_a P_b X_b) x_a) +
   gcount t (TExp (hmqv_Y t_b P_a P_b X_b)
                  (TMul {[+ hmqv_m t_a X_a P_b; p_a +]})))%Z.
Proof. by rewrite /hmqv_K gcount_TGMul_disj_union !TGMul_singleton. Qed.

#[local] Lemma gcount_hmqv_Y t t_b P_a P_b X_b :
  gcount t (hmqv_Y t_b P_a P_b X_b) =
  (gcount t X_b + gcount t (TExp P_b (hmqv_m t_b X_b P_a)))%Z.
Proof. by rewrite /hmqv_Y gcount_TGMul_disj_union !TGMul_singleton. Qed.

#[local] Lemma gfactors_hmqv_Y t_b P_a P_b X_b u :
  u ∈ gfactors (hmqv_Y t_b P_a P_b X_b) →
  u ∈ gfactors X_b ∨
  ∃ u1, u1 ∈ gfactors P_b ∧ u = TExp u1 (hmqv_m t_b X_b P_a).
Proof.
rewrite /hmqv_Y => /elem_of_gfactors_TGMul2 [uX|]; first by left.
by rewrite gfactors_TExp => /SMS.elem_of_map [u1 [-> u1P]]; right; exists u1.
Qed.

#[local] Lemma count_expo_hmqv_Y_free h t_b P_a P_b X_b u :
  u ∈ gfactors (hmqv_Y t_b P_a P_b X_b) →
  (∀ v, v ∈ gfactors X_b → count h (expo v) = 0%Z) →
  (∀ v, v ∈ gfactors P_b → count h (expo v) = 0%Z) →
  h ≠ hmqv_m t_b X_b P_a →
  count h (expo u) = 0%Z.
Proof.
move=> /gfactors_hmqv_Y [uX|[u1 [u1P ->]]] frX frP ne; first exact: frX.
rewrite count_expo_TExp; last exact: Ngmul_gfactors _ _ u1P.
by rewrite (frP _ u1P) (count_atom_ne (hmqv_m_Nmul _ _ _) ne).
Qed.

#[local] Lemma count_expo_hmqv_Y_small h t_b P_a P_b X_b u :
  u ∈ gfactors (hmqv_Y t_b P_a P_b X_b) →
  tsize X_b ≤ tsize h → tsize P_b ≤ tsize h → h ≠ hmqv_m t_b X_b P_a →
  count h (expo u) = 0%Z.
Proof.
move=> u_in leX leP; apply: (count_expo_hmqv_Y_free u_in).
  by move=> v v_in; exact: count_expo_gfactors_big v_in leX.
by move=> v v_in; exact: count_expo_gfactors_big v_in leP.
Qed.

#[local] Lemma gfactors_hmqv_Y_big h t_b P_a P_b X_b u :
  u ∈ gfactors (hmqv_Y t_b P_a P_b X_b) → tsize X_b ≤ tsize h →
  count h (expo u) ≠ 0%Z →
  ∃ u1, u1 ∈ gfactors P_b ∧ u = TExp u1 (hmqv_m t_b X_b P_a).
Proof.
move=> /gfactors_hmqv_Y [uX|H] leX ne //.
by exfalso; apply: ne; exact: count_expo_gfactors_big uX leX.
Qed.

#[local] Lemma count_hmqv_m_TExp_g t X P (n : nonce) v :
  negb (is_exp g) → negb (is_gmul g) →
  v ∈ gfactors (TExp g (TNonce n)) → count (hmqv_m t X P) (expo v) = 0%Z.
Proof.
move=> gNX gNm; rewrite gfactors_TExp (gfactors_Ngmul g gNm) SMS.map_singleton.
move=> /SMS.elem_of_singleton ->.
by rewrite expo_TExp_expN // count_hmqv_m_nonce.
Qed.

#[local] Lemma hmqv_Y_cell_ne k t P_a P X c1 c2 Y' d1 d2 :
  (∀ u, u ∈ gfactors X → count (hmqv_m t X P_a) (expo u) = 0%Z) →
  (∀ u, u ∈ gfactors P → count (hmqv_m t X P_a) (expo u) = 0%Z) →
  (∀ u, u ∈ gfactors P → count k (expo u) = 0%Z) →
  (∀ u, u ∈ gfactors Y' → count (hmqv_m t X P_a) (expo u) = 0%Z) →
  count k (hmqv_m t X P_a) = 0%Z →
  count (hmqv_m t X P_a) c1 = 0%Z → count (hmqv_m t X P_a) c2 = 0%Z →
  count k c1 ≠ count k c2 →
  count (hmqv_m t X P_a) d1 = 0%Z → count (hmqv_m t X P_a) d2 = 0%Z →
  P ≠ TGMul ∅ →
  TGMul {[+ TExp (hmqv_Y t P_a P X) c1; TExp (hmqv_Y t P_a P X) c2 +]}
  ≠ TGMul {[+ TExp Y' d1; TExp Y' d2 +]}.
Proof.
move=> frX frPh frPk frY' ckh ch1 ch2 ck12 cd1 cd2 nP eK.
have [u0 u0_in] := gfactors_nonempty nP.
have Nu0 := Ngmul_gfactors _ _ u0_in.
have Nw0 := Ngmul_TExp _ (hmqv_m t X P_a) Nu0.
have chh := count_hmqv_m_diag t X P_a.
have cht : count (hmqv_m t X P_a)
    (expo (TExp (TExp u0 (hmqv_m t X P_a)) c1)) = 1%Z.
  by rewrite (count_expo_TExp _ _ _ Nw0) (count_expo_TExp _ _ _ Nu0)
             (frPh _ u0_in) chh ch1.
have ckt : count k (expo (TExp (TExp u0 (hmqv_m t X P_a)) c1))
         = count k c1.
  by rewrite (count_expo_TExp _ _ _ Nw0) (count_expo_TExp _ _ _ Nu0)
             (frPk _ u0_in) ckh.
have zX : gcount (TExp u0 (hmqv_m t X P_a)) X = 0%Z.
  apply: not_elem_of_gcount => w0X.
  have := frX _ w0X.
  by rewrite (count_expo_TExp _ _ _ Nu0) (frPh _ u0_in) chh.
have z1 : gcount (TExp (TExp u0 (hmqv_m t X P_a)) c1)
            (TExp (hmqv_Y t P_a P X) c1) = gcount u0 P.
  by rewrite gcount_TExp_cong gcount_hmqv_Y gcount_TExp_cong zX.
have z2 : gcount (TExp (TExp u0 (hmqv_m t X P_a)) c1)
            (TExp (hmqv_Y t P_a P X) c2) = 0%Z.
  apply: gcount_TExp_no_preimage => u u_in eu.
  have Nu := Ngmul_gfactors _ _ u_in.
  have := f_equal (λ v, count (hmqv_m t X P_a) (expo v)) eu.
  rewrite /= (count_expo_TExp _ _ _ Nu) ch2 cht => chu.
  have [u1 [u1_in eu1]] :
      ∃ u1, u1 ∈ gfactors P ∧ u = TExp u1 (hmqv_m t X P_a).
    case: (gfactors_hmqv_Y u_in) => [uX|//].
    by exfalso; move: chu; rewrite (frX _ uX); lia.
  subst u.
  have := f_equal (λ v, count k (expo v)) eu.
  rewrite /= (count_expo_TExp _ _ _ Nu) ckt.
  rewrite (count_expo_TExp _ _ _ (Ngmul_gfactors _ _ u1_in)) (frPk _ u1_in) ckh.
  lia.
have z3 : gcount (TExp (TExp u0 (hmqv_m t X P_a)) c1) (TExp Y' d1) = 0%Z.
  by apply: (gcount_TExp_free frY'); rewrite cht cd1.
have z4 : gcount (TExp (TExp u0 (hmqv_m t X P_a)) c1) (TExp Y' d2) = 0%Z.
  by apply: (gcount_TExp_free frY'); rewrite cht cd2.
move: (f_equal (gcount (TExp (TExp u0 (hmqv_m t X P_a)) c1)) eK).
rewrite !gcount_TGMul_disj_union !TGMul_singleton z1 z2 z3 z4.
have : gcount u0 P ≠ 0%Z by apply/gcount_neq0.
lia.
Qed.

Lemma hmqv_K_neq_unit t_a t_b (p_a x_a p_b : nonce) P_a X_a X_b :
  negb (is_exp g) → negb (is_gmul g) →
  hmqv_K t_a t_b p_a x_a P_a X_a (TExp g p_b) X_b ≠ TGMul ∅.
Proof.
move=> gNX gNm; apply: TExp_add_neq_unit.
set w := TExp (TExp g p_b) (hmqv_m t_b X_b P_a).
have lX : tsize X_b ≤ tsize (hmqv_m t_b X_b P_a).
  by have := tsize_hmqv_m_lt t_b X_b P_a; lia.
have zX : gcount w X_b = 0%Z.
  apply: not_elem_of_gcount; rewrite /w => /count_expo_gfactors_big/(_ lX).
  rewrite (count_expo_TExp _ _ _ (Ngmul_TExp _ _ gNm)) expo_TExp_expN //.
  rewrite count_hmqv_m_nonce count_hmqv_m_diag; lia.
move=> /(f_equal (gcount w)); rewrite gcount_hmqv_Y zX gcount_TGMul_empty.
rewrite /w gcount_TExp_cong (gcount_TExp_g_diag gNm); lia.
Qed.

(** The multiplier of a key separates it from a key with another multiplier,
    provided that it occurs in neither base. *)
#[local] Lemma hmqv_K_m_ne t_a t_b (p_a x_a : nonce) P_a X_a P_b X_b
    t_a' t_b' (p_a' x_a' : nonce) P_a' X_a' P_b' X_b' :
  (∀ u, u ∈ gfactors (hmqv_Y t_b P_a P_b X_b) →
     count (hmqv_m t_a X_a P_b) (expo u) = 0%Z) →
  (∀ u, u ∈ gfactors (hmqv_Y t_b' P_a' P_b' X_b') →
     count (hmqv_m t_a X_a P_b) (expo u) = 0%Z) →
  hmqv_m t_a X_a P_b ≠ hmqv_m t_a' X_a' P_b' →
  hmqv_K t_a t_b p_a x_a P_a X_a P_b X_b ≠ TGMul ∅ →
  hmqv_K t_a t_b p_a x_a P_a X_a P_b X_b
  ≠ hmqv_K t_a' t_b' p_a' x_a' P_a' X_a' P_b' X_b'.
Proof.
move=> frY frY' neA nK.
have nY : hmqv_Y t_b P_a P_b X_b ≠ TGMul ∅.
  by move=> eY; apply: nK; rewrite /hmqv_K eY !TExp_gunit TGMul_unit_l.
have [w w_in] := gfactors_nonempty nY.
set e := TMul {[+ hmqv_m t_a X_a P_b; TNonce p_a +]}.
have cw : count (hmqv_m t_a X_a P_b) (expo (TExp w e)) = 1%Z.
  rewrite (count_expo_TExp _ _ _ (Ngmul_gfactors _ _ w_in)) (frY _ w_in) /e.
  by rewrite count_hmqv_m_e count_hmqv_m_diag.
have z Y c :
    (∀ u, u ∈ gfactors Y → count (hmqv_m t_a X_a P_b) (expo u) = 0%Z) →
    count (hmqv_m t_a X_a P_b) c = 0%Z → gcount (TExp w e) (TExp Y c) = 0%Z.
  by move=> frZ cc; apply: (gcount_TExp_free frZ); rewrite cw cc.
have ce' : count (hmqv_m t_a X_a P_b)
             (TMul {[+ hmqv_m t_a' X_a' P_b'; TNonce p_a' +]}) = 0%Z.
  by rewrite count_hmqv_m_e (count_hmqv_m_neq neA).
move=> /(f_equal (gcount (TExp w e))); rewrite !gcount_hmqv_K -/e.
rewrite (z _ _ frY (count_hmqv_m_nonce _ _ _ _)) gcount_TExp_cong.
rewrite (z _ _ frY' (count_hmqv_m_nonce _ _ _ _)) (z _ _ frY' ce').
have : gcount w (hmqv_Y t_b P_a P_b X_b) ≠ 0%Z by apply/gcount_neq0.
lia.
Qed.

#[local] Lemma hmqv_K_inj_A t_a t_b (p_a x_a p_a' x_a' : nonce)
    P_a X_a P_b X_b P_a' X_a' P_b' X_b' :
  t_a ≠ t_b →
  tsize X_b  < tsize (hmqv_m t_a X_a P_b) →
  tsize X_b' < tsize (hmqv_m t_a X_a P_b) →
  tsize P_b' < tsize (hmqv_m t_a X_a P_b) →
  hmqv_K t_a t_b p_a x_a P_a X_a P_b X_b ≠ TGMul ∅ →
  hmqv_K t_a t_b p_a x_a P_a X_a P_b X_b
  = hmqv_K t_a t_b p_a' x_a' P_a' X_a' P_b' X_b' →
  X_a = X_a' ∧ P_b = P_b'.
Proof.
move=> tab ltX ltX' ltP' nK eK.
case: (decide (hmqv_m t_a X_a P_b = hmqv_m t_a X_a' P_b'))
  => [/hmqv_m_inj [_ [? ?]] //|neA]; exfalso.
have ltP : tsize P_b < tsize (hmqv_m t_a X_a P_b).
  by exact: tsize_hmqv_m_lt2.
apply: (hmqv_K_m_ne _ _ neA nK eK).
- move=> u u_in; apply: (count_expo_hmqv_Y_small u_in); try lia.
  by case/hmqv_m_inj.
- move=> u u_in; apply: (count_expo_hmqv_Y_small u_in); try lia.
  by case/hmqv_m_inj.
Qed.

#[local] Lemma hmqv_K_inj_B t_a t_b (p_a x_a p_a' x_a' : nonce)
    P_a X_a P_b X_b P_a' X_a' P_b' X_b' :
  t_a ≠ t_b →
  tsize P_b  < tsize (hmqv_m t_b X_b P_a) →
  tsize X_b' < tsize (hmqv_m t_b X_b P_a) →
  tsize P_b' < tsize (hmqv_m t_b X_b P_a) →
  P_b ≠ TGMul ∅ →
  hmqv_K t_a t_b p_a x_a P_a X_a P_b X_b
  = hmqv_K t_a t_b p_a' x_a' P_a' X_a' P_b' X_b' →
  X_b = X_b' ∧ P_a = P_a'.
Proof.
move=> tab ltP ltX' ltP' nP eK.
case: (decide (hmqv_m t_b X_b P_a = hmqv_m t_b X_b' P_a'))
  => [/hmqv_m_inj [_ [? ?]] //|neB]; exfalso.
have tba : t_b ≠ t_a by congruence.
have ltX : tsize X_b < tsize (hmqv_m t_b X_b P_a).
  by exact: tsize_hmqv_m_lt.
have ltPA : tsize P_b < tsize (hmqv_m t_a X_a P_b).
  by exact: tsize_hmqv_m_lt2.
move: eK; rewrite /hmqv_K.
apply: (hmqv_Y_cell_ne (k := hmqv_m t_a X_a P_b)).
- by move=> u u_in; apply: count_expo_gfactors_big u_in _; lia.
- by move=> u u_in; apply: count_expo_gfactors_big u_in _; lia.
- by move=> u u_in; apply: count_expo_gfactors_big u_in _; lia.
- by move=> u u_in; apply: (count_expo_hmqv_Y_small u_in); try lia.
- by rewrite count_hmqv_m_neq //; case/hmqv_m_inj.
- exact: count_hmqv_m_nonce.
- by rewrite count_hmqv_m_e count_hmqv_m_neq //; case/hmqv_m_inj.
- by rewrite count_hmqv_m_nonce count_hmqv_m_e count_hmqv_m_diag.
- exact: count_hmqv_m_nonce.
- by rewrite count_hmqv_m_e count_hmqv_m_neq //; case/hmqv_m_inj.
- exact: nP.
Qed.

#[local] Lemma hmqv_K_inj_X t_a t_b (p_a x_a p_a' x_a' : nonce)
    P_a X_a P_b X_b X_a' P_b' :
  t_a ≠ t_b →
  tsize P_b  < tsize (hmqv_m t_b X_b P_a) →
  tsize P_b' < tsize (hmqv_m t_a X_a P_b) →
  P_b ≠ TGMul ∅ →
  hmqv_K t_a t_b p_a x_a P_a X_a P_b X_b
  = hmqv_K t_a t_b p_a' x_a' P_a X_a' P_b' X_b →
  X_a = X_a' ∧ P_b = P_b'.
Proof.
move=> tab ltP ltP'A nP eK.
case: (decide (hmqv_m t_a X_a P_b = hmqv_m t_a X_a' P_b'))
  => [/hmqv_m_inj [_ [? ?]] //|neA]; exfalso.
have ltX : tsize X_b < tsize (hmqv_m t_b X_b P_a).
  by exact: tsize_hmqv_m_lt.
have ltPA : tsize P_b < tsize (hmqv_m t_a X_a P_b).
  by exact: tsize_hmqv_m_lt2.
have leXB : tsize X_b ≤ tsize (hmqv_m t_b X_b P_a) by lia.
have lePB : tsize P_b ≤ tsize (hmqv_m t_b X_b P_a) by lia.
have lePA : tsize P_b ≤ tsize (hmqv_m t_a X_a P_b) by lia.
have leP'A : tsize P_b' ≤ tsize (hmqv_m t_a X_a P_b) by lia.
have tba : t_b ≠ t_a by congruence.
have cBe : count (hmqv_m t_b X_b P_a)
             (TMul {[+ hmqv_m t_a X_a P_b; TNonce p_a +]}) = 0%Z.
  by rewrite count_hmqv_m_e count_hmqv_m_neq //; case/hmqv_m_inj.
have cBe' : count (hmqv_m t_b X_b P_a)
              (TMul {[+ hmqv_m t_a X_a' P_b'; TNonce p_a' +]}) = 0%Z.
  by rewrite count_hmqv_m_e count_hmqv_m_neq //; case/hmqv_m_inj.
have cAe' : count (hmqv_m t_a X_a P_b)
              (TMul {[+ hmqv_m t_a X_a' P_b'; TNonce p_a' +]}) = 0%Z.
  by rewrite count_hmqv_m_e count_hmqv_m_neq.
have cAB : count (hmqv_m t_a X_a P_b) (hmqv_m t_b X_b P_a) = 0%Z.
  by rewrite count_hmqv_m_neq //; case/hmqv_m_inj.
have [u0 u0_in] := gfactors_nonempty nP.
have Nu0 := Ngmul_gfactors _ _ u0_in.
have Nw0 := Ngmul_TExp _ (hmqv_m t_b X_b P_a) Nu0.
have cBu0 := count_expo_gfactors_big u0_in lePB.
have cAu0 := count_expo_gfactors_big u0_in lePA.
have cBt : count (hmqv_m t_b X_b P_a)
    (expo (TExp (TExp u0 (hmqv_m t_b X_b P_a))
                (TMul {[+ hmqv_m t_a X_a P_b; TNonce p_a +]}))) = 1%Z.
  by rewrite (count_expo_TExp _ _ _ Nw0) (count_expo_TExp _ _ _ Nu0) cBu0
             count_hmqv_m_diag cBe.
have cAt : count (hmqv_m t_a X_a P_b)
    (expo (TExp (TExp u0 (hmqv_m t_b X_b P_a))
                (TMul {[+ hmqv_m t_a X_a P_b; TNonce p_a +]}))) = 1%Z.
  by rewrite (count_expo_TExp _ _ _ Nw0) (count_expo_TExp _ _ _ Nu0) cAu0 cAB
             count_hmqv_m_e count_hmqv_m_diag.
have zX : gcount (TExp u0 (hmqv_m t_b X_b P_a)) X_b = 0%Z.
  apply: not_elem_of_gcount => w0X.
  have := count_expo_gfactors_big w0X leXB.
  by rewrite (count_expo_TExp _ _ _ Nu0) cBu0 count_hmqv_m_diag.
(* a factor raised to [c] hitting the target comes from the [B]-cell of [P] *)
have kill : ∀ P u c, (∀ v, v ∈ gfactors P →
                        count (hmqv_m t_a X_a P_b) (expo v) = 0%Z) →
    u ∈ gfactors (hmqv_Y t_b P_a P X_b) →
    TExp u c = TExp (TExp u0 (hmqv_m t_b X_b P_a))
                    (TMul {[+ hmqv_m t_a X_a P_b; TNonce p_a +]}) →
    count (hmqv_m t_b X_b P_a) c = 0%Z →
    count (hmqv_m t_a X_a P_b) c = 0%Z → False.
  move=> P u c frP u_in eu cBc cAc.
  have Nu := Ngmul_gfactors _ _ u_in.
  have := f_equal (λ v, count (hmqv_m t_b X_b P_a) (expo v)) eu.
  rewrite /= (count_expo_TExp _ _ _ Nu) cBc cBt => cBu.
  have [u1 [u1_in eu1]] :
      ∃ u1, u1 ∈ gfactors P ∧ u = TExp u1 (hmqv_m t_b X_b P_a).
    by apply: (gfactors_hmqv_Y_big u_in leXB); lia.
  subst u.
  have := f_equal (λ v, count (hmqv_m t_a X_a P_b) (expo v)) eu.
  rewrite /= (count_expo_TExp _ _ _ Nu) cAt cAc.
  rewrite (count_expo_TExp _ _ _ (Ngmul_gfactors _ _ u1_in)) (frP _ u1_in) cAB.
  lia.
have frPb : ∀ v, v ∈ gfactors P_b →
    count (hmqv_m t_a X_a P_b) (expo v) = 0%Z.
  by move=> v v_in; exact: count_expo_gfactors_big v_in lePA.
have frPb' : ∀ v, v ∈ gfactors P_b' →
    count (hmqv_m t_a X_a P_b) (expo v) = 0%Z.
  by move=> v v_in; exact: count_expo_gfactors_big v_in leP'A.
pose proof (f_equal (gcount (TExp (TExp u0 (hmqv_m t_b X_b P_a))
             (TMul {[+ hmqv_m t_a X_a P_b; TNonce p_a +]}))) eK) as key.
have zL1 : gcount (TExp (TExp u0 (hmqv_m t_b X_b P_a))
                     (TMul {[+ hmqv_m t_a X_a P_b; TNonce p_a +]}))
             (TExp (hmqv_Y t_b P_a P_b X_b) (TNonce x_a)) = 0%Z.
  apply: gcount_TExp_no_preimage => u u_in eu.
  exact: (kill _ _ _ frPb u_in eu (count_hmqv_m_nonce _ _ _ _)
            (count_hmqv_m_nonce _ _ _ _)).
have zL2 : gcount (TExp (TExp u0 (hmqv_m t_b X_b P_a))
                     (TMul {[+ hmqv_m t_a X_a P_b; TNonce p_a +]}))
             (TExp (hmqv_Y t_b P_a P_b X_b)
                (TMul {[+ hmqv_m t_a X_a P_b; TNonce p_a +]}))
           = gcount u0 P_b.
  by rewrite gcount_TExp_cong gcount_hmqv_Y gcount_TExp_cong zX.
have zR : ∀ c, count (hmqv_m t_b X_b P_a) c = 0%Z →
    count (hmqv_m t_a X_a P_b) c = 0%Z →
    gcount (TExp (TExp u0 (hmqv_m t_b X_b P_a))
              (TMul {[+ hmqv_m t_a X_a P_b; TNonce p_a +]}))
      (TExp (hmqv_Y t_b P_a P_b' X_b) c) = 0%Z.
  move=> c cBc cAc; apply: gcount_TExp_no_preimage => u u_in eu.
  exact: (kill _ _ _ frPb' u_in eu cBc cAc).
move: key; rewrite !gcount_hmqv_K zL1 zL2.
rewrite (zR _ (count_hmqv_m_nonce _ _ _ _) (count_hmqv_m_nonce _ _ _ _)).
rewrite (zR _ cBe' cAe').
have : gcount u0 P_b ≠ 0%Z by apply/gcount_neq0.
lia.
Qed.

#[local] Lemma hmqv_K_inj_Y t_a t_b (p_a x_a p_a' x_a' : nonce)
    P_a X_a P_b X_b P_a' X_b' :
  t_a ≠ t_b →
  tsize X_b  < tsize (hmqv_m t_a X_a P_b) →
  tsize X_b' < tsize (hmqv_m t_a X_a P_b) →
  tsize X_b' < tsize (hmqv_m t_b X_b P_a) →
  P_b ≠ TGMul ∅ →
  hmqv_K t_a t_b p_a x_a P_a X_a P_b X_b
  = hmqv_K t_a t_b p_a' x_a' P_a' X_a P_b X_b' →
  X_b = X_b' ∧ P_a = P_a'.
Proof.
move=> tab ltXA ltX'A ltX'B nP eK.
case: (decide (hmqv_m t_b X_b P_a = hmqv_m t_b X_b' P_a'))
  => [/hmqv_m_inj [_ [? ?]] //|neB]; exfalso.
have ltXB : tsize X_b < tsize (hmqv_m t_b X_b P_a).
  by exact: tsize_hmqv_m_lt.
have ltPA : tsize P_b < tsize (hmqv_m t_a X_a P_b).
  by exact: tsize_hmqv_m_lt2.
have lePA : tsize P_b ≤ tsize (hmqv_m t_a X_a P_b) by lia.
have frY : ∀ u, u ∈ gfactors (hmqv_Y t_b P_a P_b X_b) →
    count (hmqv_m t_a X_a P_b) (expo u) = 0%Z.
  move=> u u_in; apply: (count_expo_hmqv_Y_small u_in); try lia.
  by case/hmqv_m_inj.
have frY' : ∀ u, u ∈ gfactors (hmqv_Y t_b P_a' P_b X_b') →
    count (hmqv_m t_a X_a P_b) (expo u) = 0%Z.
  move=> u u_in; apply: (count_expo_hmqv_Y_small u_in); try lia.
  by case/hmqv_m_inj.
have frX : ∀ u, u ∈ gfactors X_b →
    count (hmqv_m t_b X_b P_a) (expo u) = 0%Z.
  by move=> u u_in; apply: count_expo_gfactors_big u_in _; lia.
have frX' : ∀ u, u ∈ gfactors X_b' →
    count (hmqv_m t_b X_b P_a) (expo u) = 0%Z.
  by move=> u u_in; apply: count_expo_gfactors_big u_in _; lia.
have cBB' := count_hmqv_m_neq neB.
have cAe : ∀ p : nonce, count (hmqv_m t_a X_a P_b)
             (TMul {[+ hmqv_m t_a X_a P_b; TNonce p +]}) = 1%Z.
  by move=> p; rewrite count_hmqv_m_e count_hmqv_m_diag.
have cAB : count (hmqv_m t_a X_a P_b) (hmqv_m t_b X_b P_a) = 0%Z.
  by rewrite count_hmqv_m_neq //; case/hmqv_m_inj.
have cAB' : count (hmqv_m t_a X_a P_b) (hmqv_m t_b X_b' P_a') = 0%Z.
  by rewrite count_hmqv_m_neq //; case/hmqv_m_inj.
case: (SMS.max_or_empty (λ u, count (hmqv_m t_b X_b P_a) (expo u))
         (gfactors P_b)) => [[um [umP um_ge]]|/gtunitP //].
case: (SMS.max_or_empty (λ u, (- count (hmqv_m t_b X_b P_a) (expo u))%Z)
         (gfactors P_b)) => [[un [unP un_le]]|/gtunitP //].
have Num := Ngmul_gfactors _ _ umP.
have Nun := Ngmul_gfactors _ _ unP.
have cAum := count_expo_gfactors_big umP lePA.
have cAun := count_expo_gfactors_big unP lePA.
case: (decide (count (hmqv_m t_b X_b P_a) (expo um) = (-1)%Z)) => [m1|nm1].
- (* every factor of [P_b] has [B]-count [-1]: use the minimum and [B'] *)
  have cun : (count (hmqv_m t_b X_b P_a) (expo un) ≤ -1)%Z.
    by have := um_ge un unP; rewrite m1 /=; lia.
  have NunB := Ngmul_TExp _ (hmqv_m t_b X_b' P_a') Nun.
  have cAt : count (hmqv_m t_a X_a P_b)
      (expo (TExp (TExp un (hmqv_m t_b X_b' P_a')) (TNonce x_a'))) = 0%Z.
    by rewrite (count_expo_TExp _ _ _ NunB) (count_expo_TExp _ _ _ Nun) cAun
               cAB' count_hmqv_m_nonce.
  have cBt : count (hmqv_m t_b X_b P_a)
      (expo (TExp (TExp un (hmqv_m t_b X_b' P_a')) (TNonce x_a')))
    = count (hmqv_m t_b X_b P_a) (expo un).
    by rewrite (count_expo_TExp _ _ _ NunB) (count_expo_TExp _ _ _ Nun) cBB'
               count_hmqv_m_nonce; lia.
  pose proof (f_equal (gcount (TExp (TExp un (hmqv_m t_b X_b' P_a'))
                                    (TNonce x_a'))) eK) as key.
  have z1 : gcount (TExp (TExp un (hmqv_m t_b X_b' P_a')) (TNonce x_a'))
              (TExp (hmqv_Y t_b P_a P_b X_b) (TNonce x_a)) = 0%Z.
    apply: gcount_TExp_no_preimage => u u_in eu.
    have := f_equal (λ v, count (hmqv_m t_b X_b P_a) (expo v)) eu.
    rewrite /= (count_expo_TExp _ _ _ (Ngmul_gfactors _ _ u_in)).
    rewrite count_hmqv_m_nonce cBt.
    case: (gfactors_hmqv_Y u_in) => [uX|[u1 [u1_in ->]]].
      by rewrite (frX _ uX); lia.
    rewrite (count_expo_TExp _ _ _ (Ngmul_gfactors _ _ u1_in)).
    rewrite count_hmqv_m_diag.
    have := un_le u1 u1_in; rewrite /=; lia.
  have z2 : gcount (TExp (TExp un (hmqv_m t_b X_b' P_a')) (TNonce x_a'))
              (TExp (hmqv_Y t_b P_a P_b X_b)
                 (TMul {[+ hmqv_m t_a X_a P_b; TNonce p_a +]})) = 0%Z.
    by apply: (gcount_TExp_free frY); rewrite cAt cAe.
  have zX' : gcount (TExp un (hmqv_m t_b X_b' P_a')) X_b' = 0%Z.
    apply: not_elem_of_gcount => w0X.
    have := frX' _ w0X.
    by rewrite (count_expo_TExp _ _ _ Nun) cBB'; lia.
  have z3 : gcount (TExp (TExp un (hmqv_m t_b X_b' P_a')) (TNonce x_a'))
              (TExp (hmqv_Y t_b P_a' P_b X_b') (TNonce x_a'))
            = gcount un P_b.
    by rewrite gcount_TExp_cong gcount_hmqv_Y gcount_TExp_cong zX'.
  have z4 : gcount (TExp (TExp un (hmqv_m t_b X_b' P_a')) (TNonce x_a'))
              (TExp (hmqv_Y t_b P_a' P_b X_b')
                 (TMul {[+ hmqv_m t_a X_a P_b; TNonce p_a' +]})) = 0%Z.
    by apply: (gcount_TExp_free frY'); rewrite cAt cAe.
  move: key; rewrite !gcount_hmqv_K z1 z2 z3 z4.
  have : gcount un P_b ≠ 0%Z by apply/gcount_neq0.
  lia.
- (* otherwise use the maximum and [B] *)
  have NumB := Ngmul_TExp _ (hmqv_m t_b X_b P_a) Num.
  have cAt : count (hmqv_m t_a X_a P_b)
      (expo (TExp (TExp um (hmqv_m t_b X_b P_a)) (TNonce x_a))) = 0%Z.
    by rewrite (count_expo_TExp _ _ _ NumB) (count_expo_TExp _ _ _ Num) cAum
               cAB count_hmqv_m_nonce.
  have cBt : count (hmqv_m t_b X_b P_a)
      (expo (TExp (TExp um (hmqv_m t_b X_b P_a)) (TNonce x_a)))
    = (count (hmqv_m t_b X_b P_a) (expo um) + 1)%Z.
    by rewrite (count_expo_TExp _ _ _ NumB) (count_expo_TExp _ _ _ Num)
               count_hmqv_m_diag count_hmqv_m_nonce; lia.
  pose proof (f_equal (gcount (TExp (TExp um (hmqv_m t_b X_b P_a))
                                    (TNonce x_a))) eK) as key.
  have zX : gcount (TExp um (hmqv_m t_b X_b P_a)) X_b = 0%Z.
    apply: not_elem_of_gcount => w0X.
    have := frX _ w0X.
    by rewrite (count_expo_TExp _ _ _ Num) count_hmqv_m_diag; lia.
  have z1 : gcount (TExp (TExp um (hmqv_m t_b X_b P_a)) (TNonce x_a))
              (TExp (hmqv_Y t_b P_a P_b X_b) (TNonce x_a)) = gcount um P_b.
    by rewrite gcount_TExp_cong gcount_hmqv_Y gcount_TExp_cong zX.
  have z2 : gcount (TExp (TExp um (hmqv_m t_b X_b P_a)) (TNonce x_a))
              (TExp (hmqv_Y t_b P_a P_b X_b)
                 (TMul {[+ hmqv_m t_a X_a P_b; TNonce p_a +]})) = 0%Z.
    by apply: (gcount_TExp_free frY); rewrite cAt cAe.
  have z3 : gcount (TExp (TExp um (hmqv_m t_b X_b P_a)) (TNonce x_a))
              (TExp (hmqv_Y t_b P_a' P_b X_b') (TNonce x_a')) = 0%Z.
    apply: gcount_TExp_no_preimage => u u_in eu.
    have := f_equal (λ v, count (hmqv_m t_b X_b P_a) (expo v)) eu.
    rewrite /= (count_expo_TExp _ _ _ (Ngmul_gfactors _ _ u_in)).
    rewrite count_hmqv_m_nonce cBt.
    case: (gfactors_hmqv_Y u_in) => [uX|[u1 [u1_in ->]]].
      by rewrite (frX' _ uX); lia.
    rewrite (count_expo_TExp _ _ _ (Ngmul_gfactors _ _ u1_in)) cBB'.
    have := um_ge u1 u1_in; rewrite /=; lia.
  have z4 : gcount (TExp (TExp um (hmqv_m t_b X_b P_a)) (TNonce x_a))
              (TExp (hmqv_Y t_b P_a' P_b X_b')
                 (TMul {[+ hmqv_m t_a X_a P_b; TNonce p_a' +]})) = 0%Z.
    by apply: (gcount_TExp_free frY'); rewrite cAt cAe.
  move: key; rewrite !gcount_hmqv_K z1 z2 z3 z4.
  have : gcount um P_b ≠ 0%Z by apply/gcount_neq0.
  lia.
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
have lPA' : tsize P_b' < tsize (hmqv_m t_a X_a' P_b').
  by exact: tsize_hmqv_m_lt2.
have lXB : tsize X_b < tsize (hmqv_m t_b X_b P_a).
  by exact: tsize_hmqv_m_lt.
have lXB' : tsize X_b' < tsize (hmqv_m t_b X_b' P_a').
  by exact: tsize_hmqv_m_lt.
have [eXa eP] : X_a = X_a' ∧ P_b = P_b'.
  by apply: (hmqv_K_inj_A tab _ _ _ nK eK); lia.
subst X_a' P_b'.
case: (Nat.le_ge_cases (tsize (hmqv_m t_b X_b' P_a'))
                       (tsize (hmqv_m t_b X_b P_a))) => [le|ge].
  have [eX ePa] : X_b = X_b' ∧ P_a = P_a'.
    by apply: (hmqv_K_inj_Y tab _ _ _ nP eK); lia.
  by subst.
have [eX ePa] : X_b' = X_b ∧ P_a' = P_a.
  by apply: (hmqv_K_inj_Y tab _ _ _ nP (eq_sym eK)); lia.
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
have lPA : tsize P_b < tsize (hmqv_m t_a X_a P_b).
  by exact: tsize_hmqv_m_lt2.
have lPA' : tsize P_b' < tsize (hmqv_m t_a X_a' P_b').
  by exact: tsize_hmqv_m_lt2.
have lXB' : tsize X_b' < tsize (hmqv_m t_b X_b' P_a').
  by exact: tsize_hmqv_m_lt.
have [eX ePa] : X_b = X_b' ∧ P_a = P_a'.
  by apply: (hmqv_K_inj_B tab _ _ _ nP eK); lia.
subst X_b' P_a'.
case: (Nat.le_ge_cases (tsize (hmqv_m t_a X_a' P_b'))
                       (tsize (hmqv_m t_a X_a P_b))) => [le|ge].
  have [eXa eP] : X_a = X_a' ∧ P_b = P_b'.
    by apply: (hmqv_K_inj_X tab _ _ nP eK); lia.
  by subst.
have [eXa eP] : X_a' = X_a ∧ P_b' = P_b.
  by apply: (hmqv_K_inj_X tab _ _ nP' (eq_sym eK)); lia.
by subst.
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
    [hmqv_K_inj'], allow the parties to agree on their identities. *)

#[local] Lemma hmqv_K_inj_cross_A t_a t_b (p_a x_a p_b x_b : nonce)
    P_a X_a P_b X_b Q_b Y_b Q_a Y_a :
  t_a ≠ t_b →
  tsize (hmqv_m t_b X_b P_a) ≤ tsize (hmqv_m t_a X_a P_b) →
  tsize (hmqv_m t_a Y_a Q_b) ≤ tsize (hmqv_m t_a X_a P_b) →
  tsize (hmqv_m t_b Y_b Q_a) ≤ tsize (hmqv_m t_a X_a P_b) →
  hmqv_K t_a t_b p_a x_a P_a X_a P_b X_b ≠ TGMul ∅ →
  hmqv_K t_a t_b p_a x_a P_a X_a P_b X_b
  = hmqv_K t_b t_a p_b x_b Q_b Y_b Q_a Y_a →
  X_a = Y_a ∧ P_b = Q_b.
Proof.
move=> tab lB lA' lB' nK eK.
case: (decide (hmqv_m t_a X_a P_b = hmqv_m t_a Y_a Q_b))
  => [/hmqv_m_inj [_ [? ?]] //|ne]; exfalso.
have tba : t_b ≠ t_a by congruence.
have lP : tsize P_b < tsize (hmqv_m t_a X_a P_b) by exact: tsize_hmqv_m_lt2.
have lX : tsize X_b < tsize (hmqv_m t_b X_b P_a) by exact: tsize_hmqv_m_lt.
have lY : tsize Y_a < tsize (hmqv_m t_a Y_a Q_b) by exact: tsize_hmqv_m_lt.
have lQ : tsize Q_a < tsize (hmqv_m t_b Y_b Q_a) by exact: tsize_hmqv_m_lt2.
apply: (hmqv_K_m_ne _ _ _ nK eK).
- move=> u u_in; apply: (count_expo_hmqv_Y_small u_in); try lia.
  by case/hmqv_m_inj.
- by move=> u u_in; apply: (count_expo_hmqv_Y_small u_in); try lia.
- by case/hmqv_m_inj.
Qed.

#[local] Lemma hmqv_K_inj_cross_B t_a t_b (p_a x_a p_b x_b : nonce)
    P_a X_a P_b X_b Q_b Y_b Q_a Y_a :
  t_a ≠ t_b →
  tsize (hmqv_m t_a X_a P_b) ≤ tsize (hmqv_m t_b X_b P_a) →
  tsize (hmqv_m t_a Y_a Q_b) ≤ tsize (hmqv_m t_b X_b P_a) →
  tsize (hmqv_m t_b Y_b Q_a) ≤ tsize (hmqv_m t_b X_b P_a) →
  P_b ≠ TGMul ∅ →
  hmqv_K t_a t_b p_a x_a P_a X_a P_b X_b
  = hmqv_K t_b t_a p_b x_b Q_b Y_b Q_a Y_a →
  X_b = Y_b ∧ P_a = Q_a.
Proof.
move=> tab lA lA' lB' nP eK.
case: (decide (hmqv_m t_b X_b P_a = hmqv_m t_b Y_b Q_a))
  => [/hmqv_m_inj [_ [? ?]] //|ne]; exfalso.
have tba : t_b ≠ t_a by congruence.
have lP : tsize P_b < tsize (hmqv_m t_a X_a P_b) by exact: tsize_hmqv_m_lt2.
have lX : tsize X_b < tsize (hmqv_m t_b X_b P_a) by exact: tsize_hmqv_m_lt.
have lY : tsize Y_a < tsize (hmqv_m t_a Y_a Q_b) by exact: tsize_hmqv_m_lt.
have lQ : tsize Q_a < tsize (hmqv_m t_b Y_b Q_a) by exact: tsize_hmqv_m_lt2.
move: eK; rewrite /hmqv_K.
apply: (hmqv_Y_cell_ne (k := hmqv_m t_a X_a P_b)).
- by move=> u u_in; apply: count_expo_gfactors_big u_in _; lia.
- by move=> u u_in; apply: count_expo_gfactors_big u_in _; lia.
- by move=> u u_in; apply: count_expo_gfactors_big u_in _; lia.
- move=> u u_in; apply: (count_expo_hmqv_Y_small u_in); try lia.
  by case/hmqv_m_inj.
- by rewrite count_hmqv_m_neq //; case/hmqv_m_inj.
- exact: count_hmqv_m_nonce.
- by rewrite count_hmqv_m_e count_hmqv_m_neq //; case/hmqv_m_inj.
- by rewrite count_hmqv_m_nonce count_hmqv_m_e count_hmqv_m_diag.
- exact: count_hmqv_m_nonce.
- by rewrite count_hmqv_m_e count_hmqv_m_neq.
- exact: nP.
Qed.

#[local] Lemma hmqv_K_inj_cross_pair t_a t_b (p_a x_a p_b x_b : nonce) X_b Q_a :
  negb (is_exp g) → negb (is_gmul g) → t_a ≠ t_b →
  hmqv_K t_a t_b p_a x_a (TExp g p_a) (TExp g x_a) (TExp g p_b) X_b
    ≠ TGMul ∅ →
  hmqv_K t_a t_b p_a x_a (TExp g p_a) (TExp g x_a) (TExp g p_b) X_b
  = hmqv_K t_b t_a p_b x_b (TExp g p_b) (TExp g x_b) Q_a (TExp g x_a) →
  X_b = TExp g x_b ∧ Q_a = TExp g p_a.
Proof.
move=> gNX gNm tab nK eK.
case: (decide (hmqv_m t_b X_b (TExp g p_a) = hmqv_m t_b (TExp g x_b) Q_a))
  => [/hmqv_m_inj [_ [? ?]] //|ne]; exfalso.
have tba : t_b ≠ t_a by congruence.
have lX : tsize X_b < tsize (hmqv_m t_b X_b (TExp g p_a)).
  by exact: tsize_hmqv_m_lt.
have lQ : tsize Q_a < tsize (hmqv_m t_b (TExp g x_b) Q_a).
  by exact: tsize_hmqv_m_lt2.
have frg : ∀ t X P (n : nonce) v, v ∈ gfactors (TExp g (TNonce n)) →
    count (hmqv_m t X P) (expo v) = 0%Z.
  by move=> t X P n v v_in; exact: count_hmqv_m_TExp_g gNX gNm v_in.
case: (Nat.le_ge_cases (tsize (hmqv_m t_b (TExp g x_b) Q_a))
                       (tsize (hmqv_m t_b X_b (TExp g p_a)))) => [le|ge].
- move: eK; rewrite /hmqv_K.
  apply: (hmqv_Y_cell_ne (k := hmqv_m t_a (TExp g x_a) (TExp g p_b))).
  + by move=> u u_in; apply: count_expo_gfactors_big u_in _; lia.
  + by move=> u u_in; apply: frg u_in.
  + by move=> u u_in; apply: frg u_in.
  + move=> u u_in; apply: (count_expo_hmqv_Y_free u_in).
    * by move=> v v_in; apply: frg v_in.
    * by move=> v v_in; apply: count_expo_gfactors_big v_in _; lia.
    * by case/hmqv_m_inj.
  + by rewrite count_hmqv_m_neq //; case/hmqv_m_inj.
  + exact: count_hmqv_m_nonce.
  + by rewrite count_hmqv_m_e count_hmqv_m_neq //; case/hmqv_m_inj.
  + by rewrite count_hmqv_m_nonce count_hmqv_m_e count_hmqv_m_diag.
  + exact: count_hmqv_m_nonce.
  + by rewrite count_hmqv_m_e count_hmqv_m_neq.
  + exact: Ngmul_neq_unit (Ngmul_TExp _ _ gNm).
- apply: (hmqv_K_m_ne _ _ _ _ (eq_sym eK)).
  + move=> u u_in; apply: (count_expo_hmqv_Y_free u_in).
    * by move=> v v_in; apply: frg v_in.
    * by move=> v v_in; apply: count_expo_gfactors_big v_in _; lia.
    * by case/hmqv_m_inj.
  + move=> u u_in; apply: (count_expo_hmqv_Y_free u_in).
    * by move=> v v_in; apply: count_expo_gfactors_big v_in _; lia.
    * by move=> v v_in; apply: frg v_in.
    * exact: not_eq_sym ne.
  + by case/hmqv_m_inj.
  + by rewrite -eK.
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
have fin1 : TExp g x_a = Y_a → P_b = TExp g p_b →
    P_b = TExp g p_b ∧ X_b = TExp g x_b ∧ Q_a = TExp g p_a ∧
    Y_a = TExp g x_a.
  move=> eY eP; subst Y_a P_b.
  have [eX eQ] := hmqv_K_inj_cross_pair gNX gNm tab nK eK.
  by subst.
have fin2 : X_b = TExp g x_b → TExp g p_a = Q_a →
    P_b = TExp g p_b ∧ X_b = TExp g x_b ∧ Q_a = TExp g p_a ∧
    Y_a = TExp g x_a.
  move=> eX eQ; subst X_b Q_a.
  have [eY eP] := hmqv_K_inj_cross_pair gNX gNm tba nK' (eq_sym eK).
  by subst.
set a  := tsize (hmqv_m t_a (TExp g x_a) P_b).
set b  := tsize (hmqv_m t_b X_b (TExp g p_a)).
set a' := tsize (hmqv_m t_a Y_a (TExp g p_b)).
set b' := tsize (hmqv_m t_b (TExp g x_b) Q_a).
have : (b ≤ a ∧ a' ≤ a ∧ b' ≤ a) ∨ (a ≤ b ∧ a' ≤ b ∧ b' ≤ b) ∨
       (a ≤ a' ∧ b ≤ a' ∧ b' ≤ a') ∨ (a ≤ b' ∧ b ≤ b' ∧ a' ≤ b') by lia.
case=> [[h1 [h2 h3]]|[[h1 [h2 h3]]|[[h1 [h2 h3]]|[h1 [h2 h3]]]]].
- have [eXa eP] := hmqv_K_inj_cross_A tab h1 h2 h3 nK eK.
  exact: fin1 eXa eP.
- have [eX eQ] := hmqv_K_inj_cross_B tab h1 h2 h3 nP eK.
  exact: fin2 eX eQ.
- have [eY eP] := hmqv_K_inj_cross_B tba h3 h2 h1 nQ (eq_sym eK).
  exact: fin1 (eq_sym eY) (eq_sym eP).
- have [eX eQ] := hmqv_K_inj_cross_A tba h3 h2 h1 nK' (eq_sym eK).
  exact: fin2 (eq_sym eX) (eq_sym eQ).
Qed.

(** ** Binding a claimed key by freshness

    [hmqv_K_inj'] binds a responder's key to the long-term key [P] that its
    peer claimed only if [P] is not the identity.  Freshness can replace that
    check.  Suppose the responder's ephemeral private key [x_b'] differs from
    its long-term private key and occurs neither in [P] nor in the share
    [X_a'] it received.  Then an initiator that computes the same key still
    learns that [P] is its own long-term key.  Freshness plays the role of the
    size argument of [gcount_TExp_eq0]: a term that contains [x_b'] cannot
    occur in [P] or in [X_a']. *)

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
set m_a  := hmqv_m t_a (TExp g x_a) (TExp g p_b).
set m_b  := hmqv_m t_b X_b (TExp g p_a).
set m_a' := hmqv_m t_a X_a' (TExp g p_b').
set m_b' := hmqv_m t_b (TExp g x_b') P.
case: (decide (m_b = m_b')) => [|neb].
  by rewrite /m_b /m_b' => /hmqv_m_inj [] _ [] _ ->.
exfalso.
set ss := hmqv_ss t_a t_b p_a (TExp g p_a) (TExp g x_a) p_b X_b.
have : (0 < gcount ss (hmqv_K t_b t_a p_b' x_b' (TExp g p_b') (TExp g x_b')
                              P X_a'))%Z.
  by apply/gcount_gt0; rewrite -eK; apply: hmqv_K_gfactor => //; right.
rewrite /hmqv_K /hmqv_Y -/m_a' -/m_b'.
rewrite !TExp_TGMul !SMS.map_disj_union !SMS.map_singleton !TExpA.
rewrite -TGMul_disj_union !gcount_TGMul_disj_union !TGMul_singleton.
have tags X X' Q Q' : hmqv_m t_a X Q ≠ hmqv_m t_b X' Q'.
  by move=> /hmqv_m_inj [] e _; apply: tab.
have exps_ss u :
    u ∈ exps ss ↔ u = TNonce p_b ∨ u = m_b ∨ u = m_a ∨ u = TNonce p_a.
  rewrite /ss exps_hmqv_ss // SMS.elem_of_make_nil_r.
  by rewrite !elem_of_cons elem_of_nil; intuition.
have mb_ma' : m_b ≠ m_a' := not_eq_sym (tags _ _ _ _).
have mb'_ma' : m_b' ≠ m_a' := not_eq_sym (tags _ _ _ _).
have ma_ma' : x_b' = p_b → m_a ≠ m_a'.
  rewrite /m_a /m_a' => e_b /hmqv_m_inj [] _ [] _ /(TExp_injr gN1) [].
  by move=> e_p; apply: ne_x; rewrite e_b.
have mb'_ss : m_b' ∉ exps ss.
  rewrite exps_ss => - [|[|[|]]] //.
  by move=> e; apply: (tags _ _ _ _ (eq_sym e)).
have x_mb' : subterm (TNonce x_b') m_b'.
  by rewrite /m_b'; apply: subterm_hmqv_m; left; exact: subterm_TExp_g.
(* If [x_b'] is one of the long-term keys in [ss], a multiplier of [ss]
   contains [x_b'], so [X] cannot provide it. *)
have zx X c :
    ¬ subterm (TNonce x_b') X → TNonce x_b' ∈ factors c → m_b ∉ factors c →
    (x_b' = p_b → m_a ∉ factors c) →
    gcount ss (TExp X c) = 0%Z.
  move=> fr x_c mb_c ma_c.
  case: (decide (x_b' = p_a)) => [e|ne_a].
    apply: (gcount_TExp_fresh (u := m_b) (n := TNonce x_b')) => //.
      by rewrite exps_ss; eauto.
    by rewrite /m_b -e; apply: subterm_hmqv_m; right; exact: subterm_TExp_g.
  case: (decide (x_b' = p_b)) => [e|ne_b].
    apply: (gcount_TExp_fresh (u := m_a) (n := TNonce x_b')) => //.
    - by rewrite exps_ss; eauto.
    - exact: ma_c.
    - by rewrite /m_a -e; apply: subterm_hmqv_m; right; exact: subterm_TExp_g.
  apply: (gcount_TExp_fresh_exp (u := TNonce x_b') (n := TNonce x_b')) => //.
  by rewrite exps_ss => - [[]|[|[|[]]]].
have z1 : gcount ss (TExp X_a' (TNonce x_b')) = 0%Z.
  apply: zx => //; first by rewrite elem_of_factors_Nmul.
  - exact: not_elem_of_factors_atom.
  - by move=> _; exact: not_elem_of_factors_atom.
have z2 : gcount ss (TExp P (TMul {[+ m_a'; TNonce x_b' +]})) = 0%Z.
  apply: zx => //.
  - rewrite -count_neq0 count_TMul_disj_union !TMul_singleton.
    by rewrite count_atom_ne // count_atom_diag.
  - apply: not_elem_of_factors_TMul => u.
    by case/SMS.elem_of_disj_union => /SMS.elem_of_singleton ->.
  - move=> /ma_ma' ?; apply: not_elem_of_factors_TMul => u.
    by case/SMS.elem_of_disj_union => /SMS.elem_of_singleton ->.
have z3 : gcount ss (TExp X_a' (TMul {[+ m_b'; TNonce p_b' +]})) = 0%Z.
  apply: (gcount_TExp_fresh_exp (u := m_b') (n := TNonce x_b')) => //.
  rewrite -count_neq0 count_TMul_disj_union !TMul_singleton.
  by rewrite count_atom_diag // count_atom_ne.
have z4 :
    gcount ss (TExp P (TMul {[+ m_a'; TMul {[+ m_b'; TNonce p_b' +]} +]}))
    = 0%Z.
  apply: (gcount_TExp_fresh_exp (u := m_b') (n := TNonce x_b')) => //.
  rewrite -count_neq0 !count_TMul_disj_union !TMul_singleton.
  rewrite count_TMul_disj_union !TMul_singleton.
  by rewrite count_atom_ne // count_atom_diag // count_atom_ne.
by rewrite z1 z2 z3 z4; lia.
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
