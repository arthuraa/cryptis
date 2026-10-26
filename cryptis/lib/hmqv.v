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
      which long-term and ephemeral keys were used.  If the agents' long-term
      keys represent their identity, this means that the key binds who
      participated in the key exchange, an authentication guarantee.  Moreover,
      if ephemeral keys are used only once, this guarantees that session keys
      are fresh.

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

Lemma hmqv_m_inj t t' X X' P P' :
  hmqv_m t X P = hmqv_m t' X' P' -> t = t' /\ X = X' /\ P = P'.
Proof.
rewrite /hmqv_m => - [] /Spec.tag_inj [] /Tag_inj c /Spec.of_list_inj [] -> ->.
by case: (ndot_inj _ _ _ _ c).
Qed.

Lemma tsize_hmqv_m_lt t X P : tsize X < tsize (hmqv_m t X P).
Proof.
rewrite /hmqv_m [Spec.tag]unlock.
have e : tsize (THash (TPair (Tag (N.@t)) (Spec.of_list [X; P])))
       = S (S (tsize (Tag (N.@t)) + tsize (Spec.of_list [X; P]))).
  by rewrite [tsize (THash _)]tsize_eq [tsize (TPair _ _)]tsize_eq.
rewrite e.
have X_in : X ∈ [X; P] by set_solver.
have := Spec.of_list_tsize X_in; lia.
Qed.

Definition hmqv_Y (t_b : string) (P_a P_b X_b : term) : term :=
  TGMul {[+ X_b; TExp P_b (hmqv_m t_b X_b P_a) +]}.

Definition hmqv_K (t_a t_b : string) (p_a x_a P_a X_a P_b X_b : term) : term :=
  TGMul {[+ TExp (hmqv_Y t_b P_a P_b X_b) x_a;
            TExp (hmqv_Y t_b P_a P_b X_b) (TMul {[+ hmqv_m t_a X_a P_b; p_a +]})
         +]}.

(** The largest factor of the HMQV key, measured in the number of exponents. *)

Definition hmqv_ss (t_a t_b : string) (p_a P_a X_a p_b X_b : term) : term :=
  TExp g (TMul {[+ p_b; hmqv_m t_b X_b P_a; hmqv_m t_a X_a (TExp g p_b);
                   p_a +]}).

Lemma hmqv_K_expand t_a t_b p_a x_a P_a X_a p_b X_b :
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

Lemma gcount_TExp_g_diag :
  negb (is_gmul g) → ∀ s, gcount (TExp g s) (TExp g s) = 1%Z.
Proof.
move=> gNm s; rewrite gcount_diag; by case: is_gmul (Ngmul_TExp _ s gNm).
Qed.

Lemma gcount_TExp_g_ge0 :
  negb (is_gmul g) → ∀ s1 s2, (0 <= gcount (TExp g s1) (TExp g s2))%Z.
Proof. by move=> gNm s1 s2; apply: gcount_atom_ge0; apply: Ngmul_TExp. Qed.

Lemma exps_hmqv_ss t_a t_b (p_a p_b : nonce) P_a X_a X_b :
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

Lemma exps_hmqv_mixed t_b (p_b x_a : nonce) P_a X_b :
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

Lemma hmqv_K_gfactor t_a t_b (p_a x_a p_b : nonce) P_a X_a X_b s :
  negb (is_exp g) → negb (is_gmul g) →
  let m_a := hmqv_m t_a X_a (TExp g p_b) in
  let m_b := hmqv_m t_b X_b P_a in
  t_a ≠ t_b ->
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
have := @gcount_TExp_g_ge0 gNm e3 e4.
have := @gcount_TExp_g_ge0 gNm e4 e3.
by case: Hs => ->; rewrite (gcount_TExp_g_diag gNm); lia.
Qed.

Lemma hmqv_key_gfactors t_a t_b (p_a x_a p_b : nonce) P_a X_a X_b :
  negb (is_exp g) → negb (is_gmul g) →
  let m_b := hmqv_m t_b X_b P_a in
  let ss := hmqv_ss t_a t_b p_a P_a X_a p_b X_b in
  let K := hmqv_K t_a t_b p_a x_a P_a X_a (TExp g p_b) X_b in
  t_a ≠ t_b ->
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

Lemma hmqv_K_gfactor_eph t_a t_b (p_a x_a p_b x_b : nonce) P_a X_a :
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
have := @gcount_TExp_g_ge0 gNm e e2.
have := @gcount_TExp_g_ge0 gNm e e3.
have := @gcount_TExp_g_ge0 gNm e e4.
lia.
Qed.

(** The following result is crucial to establish agreement.  It tells us that,
    if two sets of key parameters do _not_ agree, then the static-static factor
    [hmqv_ss] corresponding to one set cannot occur in the session key of the
    other set.

    Note that the hypothesis [tsize X_b' < tsize m_b] is required.  Otherwise,
    we can set [p_a' = p_a], [x_a' = x_a], [p_b' = p_b] and
    [X_b' = g ^ (p_b ⋅ m_b)]. Even though [X_b' ≠ X_b], because of
    [hmqv_K_expand], [hmqv_ss t_a t_b p_a P_a X_a p_b X_b = X_b' ^ (p_a ⋅ m_a)]
    occurs in [hmqv_K t_a t_b p_a' x_a' P_a' X_a' P_b' X_b'].  This won't be a
    problem when proving agreement later because we can always this condition
    to hold.

*)

Lemma gcount_ss_hmqv_K t_a t_b (p_a x_a p_b p_a' x_a' p_b' : nonce) X_b X_b' :
  negb (is_exp g) → negb (is_gmul g) →
  let m_b := hmqv_m t_b X_b (TExp g p_a) in
  t_a ≠ t_b ->
  tsize X_b' < tsize m_b ->
  gcount (hmqv_ss t_a t_b p_a (TExp g p_a) (TExp g x_a) p_b X_b)
         (hmqv_K t_a t_b p_a' x_a' (TExp g p_a') (TExp g x_a')
                 (TExp g p_b') X_b')
  = if bool_decide (p_a = p_a' ∧ x_a = x_a' ∧ p_b = p_b' ∧ X_b = X_b')
    then 1%Z else 0%Z.
Proof.
move=> gNX gNm m_b tab ltX.
set m_a  := hmqv_m t_a (TExp g x_a) (TExp g p_b).
set m_a' := hmqv_m t_a (TExp g x_a') (TExp g p_b').
set m_b' := hmqv_m t_b X_b' (TExp g p_a').
set ss   := hmqv_ss t_a t_b p_a (TExp g p_a) (TExp g x_a) p_b X_b.
set ss'  := hmqv_ss t_a t_b p_a' (TExp g p_a') (TExp g x_a') p_b' X_b'.
have mb_ma' : m_b ≠ m_a'.
  by rewrite /m_b /m_a' => /hmqv_m_inj [] e _; apply: tab; congruence.
have ma_mb' : m_a ≠ m_b'.
  by rewrite /m_a /m_b' => /hmqv_m_inj [] e _; apply: tab; congruence.
have exps4 :
    exps ss = SMS.make [TNonce p_b; m_b; m_a; TNonce p_a] [].
  by rewrite /ss /m_a /m_b exps_hmqv_ss.
have exps4' :
    exps ss' =
    SMS.make [TNonce p_b'; m_b'; m_a'; TNonce p_a'] [].
  by rewrite /ss' /m_a' /m_b' exps_hmqv_ss.
have mb_4 : m_b ∈ exps ss by rewrite exps4 SMS.elem_of_make_nil_r; set_solver.
have ma_4 : m_a ∈ exps ss by rewrite exps4 SMS.elem_of_make_nil_r; set_solver.
(* The cross terms: [m_b] is an exponent of the counted factor, but of nothing
   [X_b'] gets raised to, and [X_b'] is smaller than it. *)
have mb_x : m_b ∉ factors (TNonce x_a') by apply: not_elem_of_factors_atom.
have mb_ma_pa : m_b ∉ factors (TMul {[+ m_a'; TNonce p_a' +]}).
  apply: not_elem_of_factors_TMul => u.
  by case/SMS.elem_of_disj_union => /SMS.elem_of_singleton ->.
have z1 : gcount ss (TExp X_b' (TNonce x_a')) = 0%Z
  := gcount_TExp_eq0 X_b' (TNonce x_a') _ m_b mb_4 mb_x ltX.
have z3 : gcount ss (TExp X_b' (TMul {[+ m_a'; TNonce p_a' +]})) = 0%Z
  := gcount_TExp_eq0 X_b' _ _ m_b mb_4 mb_ma_pa ltX.
(* The ephemeral factor has three exponents, the counted one four. *)
have z2 : gcount ss (TExp g (TMul {[+ TNonce p_b'; m_b'; TNonce x_a' +]}))
          = 0%Z.
  have ne : ss ≠ TExp g (TMul {[+ TNonce p_b'; m_b'; TNonce x_a' +]}).
    move=> e; move: ma_4; rewrite e exps_TExp_expN //.
    apply: not_elem_of_factors_TMul => u; repeat case/SMS.elem_of_disj_union;
    by move=> /SMS.elem_of_singleton ->.
  have nin : ss ∉ gfactors
                   (TExp g (TMul {[+ TNonce p_b'; m_b'; TNonce x_a' +]})).
    by rewrite (elem_of_gfactors_Ngmul _ (Ngmul_TExp _ _ gNm)).
  exact: not_elem_of_gcount _ _ nin.
rewrite hmqv_K_expand -/m_a' -/m_b' -/ss' !gcount_TGMul_disj_union.
rewrite !TGMul_singleton z1 z2 z3.
case_bool_decide as cond.
- case: cond => epa [exa [epb eXb]].
  have -> : ss' = ss by rewrite /ss' /ss epa exa epb eXb.
  by rewrite /ss /hmqv_ss (gcount_TExp_g_diag gNm).
- have ne : ss ≠ ss'.
    move=> e4; apply: cond.
    have perm : [TNonce p_b; m_b; m_a; TNonce p_a]
                ≡ₚ [TNonce p_b'; m_b'; m_a'; TNonce p_a'].
      rewrite -(SMS.pos_make_nil_r [TNonce p_b; m_b; m_a; TNonce p_a]).
      by rewrite -exps4 e4 exps4' SMS.pos_make_nil_r.
    have ema : m_a = m_a'.
      have : m_a ∈ [TNonce p_b'; m_b'; m_a'; TNonce p_a'] by rewrite -perm; set_solver.
      by rewrite !elem_of_cons elem_of_nil; case=> [|[|[|[|[]]]]].
    have emb : m_b = m_b'.
      have : m_b ∈ [TNonce p_b'; m_b'; m_a'; TNonce p_a'] by rewrite -perm; set_solver.
      by rewrite !elem_of_cons elem_of_nil; case=> [|[|[|[|[]]]]].
    move: (ema); rewrite /m_a /m_a' => /hmqv_m_inj [] _ [] exa epb.
    move/(f_equal expo): exa; rewrite !expo_TExp_expN //; case=> exa.
    move/(f_equal expo): epb; rewrite !expo_TExp_expN //; case=> epb.
    move: (emb); rewrite /m_b /m_b' => /hmqv_m_inj [] _ [] eXb ePa.
    move/(f_equal expo): ePa; rewrite !expo_TExp_expN //; case=> epa.
    by do !split => //.
  have nin : ss ∉ gfactors ss'.
    by rewrite /ss' /hmqv_ss (elem_of_gfactors_Ngmul _ (Ngmul_TExp _ _ gNm)).
  have := not_elem_of_gcount _ _ nin; lia.
Qed.

(** The following lemma says that a session key uniquely determines which keys
    were used to compute it. Note that we must assume that the peer's key [P_b]
    is a well formed HMQV public key.  Otherwise, fix [X_b1] and [X_b2],
    and pose [P_bk = (X_bk^{-1})^{m_bk^{-1}}], which can be computed from the
    long-term public key [P_a].  We have [Y_bk = X_bkP_bk^m_bk = 1], which
    implies that

       hmqv_K t_a t_b p_a x_a1 P_a X_a1 P_b1 X_b1 =
       hmqv_K t_a t_b p_a x_a2 P_a X_a2 P_b2 X_b2

    regardless of the ephemeral private key [x_a].  In other words, giving
    the attacker the flexibility to choose [P_b] leads to a session key that
    does not bind the ephemeral nor the other party's identity.
*)

Lemma hmqv_K_inj t_a t_b (p_a x_a p_b p_a' x_a' p_b' : nonce) X_b X_b' :
  negb (is_exp g) → negb (is_gmul g) →
  t_a ≠ t_b ->
  hmqv_K t_a t_b p_a x_a (TExp g p_a) (TExp g x_a) (TExp g p_b) X_b
  = hmqv_K t_a t_b p_a' x_a' (TExp g p_a') (TExp g x_a') (TExp g p_b') X_b' ->
  p_a = p_a' /\ x_a = x_a' /\ p_b = p_b' /\ X_b = X_b'.
Proof.
move=> gNX gNm tab eK.
set m_b  := hmqv_m t_b X_b (TExp g p_a).
set m_b' := hmqv_m t_b X_b' (TExp g p_a').
have in4 : (0 < gcount (hmqv_ss t_a t_b p_a (TExp g p_a) (TExp g x_a) p_b X_b)
                   (hmqv_K t_a t_b p_a' x_a' (TExp g p_a') (TExp g x_a')
                           (TExp g p_b') X_b'))%Z.
  apply/gcount_gt0; rewrite -eK; apply: hmqv_K_gfactor => //; by right.
have in4' :
    (0 < gcount (hmqv_ss t_a t_b p_a' (TExp g p_a') (TExp g x_a') p_b' X_b')
                (hmqv_K t_a t_b p_a x_a (TExp g p_a) (TExp g x_a)
                        (TExp g p_b) X_b))%Z.
  apply/gcount_gt0; rewrite eK; apply: hmqv_K_gfactor => //; by right.
have ltb : tsize X_b < tsize m_b by exact: tsize_hmqv_m_lt.
have ltb' : tsize X_b' < tsize m_b' by exact: tsize_hmqv_m_lt.
case: (decide (tsize X_b' < tsize m_b)) => [lt|le].
- move: in4.
  have E := @gcount_ss_hmqv_K t_a t_b p_a x_a p_b p_a' x_a' p_b'
                              X_b X_b' gNX gNm tab lt.
  cbv zeta in E; rewrite E; case_bool_decide as cond; last by lia.
  by case: cond => ? [? [? ?]].
- move: in4'.
  have lt' : tsize X_b < tsize m_b' by lia.
  have E := @gcount_ss_hmqv_K t_a t_b p_a' x_a' p_b' p_a x_a p_b
                              X_b' X_b gNX gNm tab lt'.
  cbv zeta in E; rewrite E; case_bool_decide as cond; last by lia.
  by case: cond => ? [? [? ?]].
Qed.

(** ** Identity binding when receiving messages

    The [hmqv_K_inj] lemma does not cover all agreement properties that
    we need. When one party runs the protocol, they cannot guarantee that
    the other party's ephemeral public key was generated as prescribed by
    the protocol, because it is sent out in the clear, unauthenticated.

    Now, consider what happens when party [a] receives a message encrypted
    with a session key [K] exchanged with [b].  From [a]'s perspective, this
    key is of the form [hmqv_K t_a t_b p_a x_a P_a X_a P_b X_b].  If the
    message's encryption predicate guaranteed that this key were of the form
    [hmqv_K t_a t_b p_a' x_a' P_a' X_a' P_b' X_b'], we could use [hmqv_K_inj]
    to prove that these parameters are equal and that the message was indeed
    sent by the other party.  However, [b] would be unable to prove such a
    predicate, since, from their perspective, they don't know that such an
    [x_a'] exists: all they know is that _some_ [X_a'] was used to compute
    [K].  Therefore, [a] must be able to establish agreement even when the
    message's predicate only guarantees that [K] is of the form
    [hmqv_K t_b t_a p_b' x_b' P_b' X_b' P_a' X_a'].  This is the job of
    [hmqv_K_inj'], whose proof relies on the following variant of
    [gcount_ss_hmqv_K].
*)

Lemma gcount_ss_hmqv_K_cross t_a t_b (p_a x_a p_b p_a' x_b' p_b' : nonce)
    X_b X_a' :
  negb (is_exp g) → negb (is_gmul g) →
  let m_a  := hmqv_m t_a (TExp g x_a) (TExp g p_b) in
  let m_b  := hmqv_m t_b X_b (TExp g p_a) in
  let m_b' := hmqv_m t_b (TExp g x_b') (TExp g p_a') in
  let m_a' := hmqv_m t_a X_a' (TExp g p_b') in
  t_a ≠ t_b ->
  m_a ≠ m_a' -> m_b ≠ m_b' ->
  tsize X_a' < tsize m_b ->
  gcount (hmqv_ss t_a t_b p_a (TExp g p_a) (TExp g x_a) p_b X_b)
         (hmqv_K t_b t_a p_b' x_b' (TExp g p_b') (TExp g x_b')
                 (TExp g p_a') X_a')
  = 0%Z.
Proof.
move=> gNX gNm m_a m_b m_b' m_a' tab nea neb ltX.
set ss  := hmqv_ss t_a t_b p_a (TExp g p_a) (TExp g x_a) p_b X_b.
set ss' := hmqv_ss t_b t_a p_b' (TExp g p_b') (TExp g x_b') p_a' X_a'.
have ma_mb' : m_a ≠ m_b'.
  by rewrite /m_a /m_b' => /hmqv_m_inj [] e _; apply: tab; congruence.
have exps4 :
    exps ss = SMS.make [TNonce p_b; m_b; m_a; TNonce p_a] [].
  by rewrite /ss /m_a /m_b exps_hmqv_ss.
have mb_4 : m_b ∈ exps ss by rewrite exps4 SMS.elem_of_make_nil_r; set_solver.
have ma_4 : m_a ∈ exps ss by rewrite exps4 SMS.elem_of_make_nil_r; set_solver.
have mb_x : m_b ∉ factors (TNonce x_b') by apply: not_elem_of_factors_atom.
have mb_mb_pb : m_b ∉ factors (TMul {[+ m_b'; TNonce p_b' +]}).
  apply: not_elem_of_factors_TMul => u.
  by case/SMS.elem_of_disj_union => /SMS.elem_of_singleton ->.
have z1 : gcount ss (TExp X_a' (TNonce x_b')) = 0%Z
  := gcount_TExp_eq0 X_a' (TNonce x_b') _ m_b mb_4 mb_x ltX.
have z3 : gcount ss (TExp X_a' (TMul {[+ m_b'; TNonce p_b' +]})) = 0%Z
  := gcount_TExp_eq0 X_a' _ _ m_b mb_4 mb_mb_pb ltX.
(* [m_a] is an exponent of the counted factor but of neither remaining one. *)
have z2 : gcount ss (TExp g (TMul {[+ TNonce p_a'; m_a'; TNonce x_b' +]}))
          = 0%Z.
  have ne : ss ≠ TExp g (TMul {[+ TNonce p_a'; m_a'; TNonce x_b' +]}).
    move=> e; move: ma_4; rewrite e exps_TExp_expN //.
    apply: not_elem_of_factors_TMul => u; repeat case/SMS.elem_of_disj_union;
    by move=> /SMS.elem_of_singleton ->.
  have nin : ss ∉ gfactors
                   (TExp g (TMul {[+ TNonce p_a'; m_a'; TNonce x_b' +]})).
    by rewrite (elem_of_gfactors_Ngmul _ (Ngmul_TExp _ _ gNm)).
  exact: not_elem_of_gcount _ _ nin.
have z4 : gcount ss ss' = 0%Z.
  have ne : ss ≠ ss'.
    move=> e; move: ma_4.
    rewrite e /ss' /hmqv_ss -/m_a' -/m_b' exps_TExp_expN //.
    apply: not_elem_of_factors_TMul => u; repeat case/SMS.elem_of_disj_union;
    by move=> /SMS.elem_of_singleton ->.
  have nin : ss ∉ gfactors ss'.
    by rewrite /ss' /hmqv_ss (elem_of_gfactors_Ngmul _ (Ngmul_TExp _ _ gNm)).
  exact: not_elem_of_gcount _ _ nin.
rewrite hmqv_K_expand -/m_a' -/m_b' -/ss' !gcount_TGMul_disj_union.
by rewrite !TGMul_singleton z1 z2 z3 z4; lia.
Qed.

Lemma hmqv_K_inj' t_a t_b (p_a x_a p_b p_a' x_b' p_b' : nonce) X_b X_a' :
  negb (is_exp g) → negb (is_gmul g) →
  t_a ≠ t_b ->
  hmqv_K t_a t_b p_a x_a (TExp g p_a) (TExp g x_a) (TExp g p_b) X_b
  = hmqv_K t_b t_a p_b' x_b' (TExp g p_b') (TExp g x_b') (TExp g p_a') X_a' ->
  p_a = p_a' /\ p_b = p_b' /\ X_b = TExp g x_b' /\ X_a' = TExp g x_a.
Proof.
move=> gNX gNm tab eK.
set m_a  := hmqv_m t_a (TExp g x_a) (TExp g p_b).
set m_b  := hmqv_m t_b X_b (TExp g p_a).
set m_b' := hmqv_m t_b (TExp g x_b') (TExp g p_a').
set m_a' := hmqv_m t_a X_a' (TExp g p_b').
have tba : t_b ≠ t_a by congruence.
case: (decide (m_a = m_a')) => [ema|nea].
  move: (ema); rewrite /m_a /m_a' => /hmqv_m_inj [] _ [] eXa epb.
  move/(f_equal expo): epb; rewrite !expo_TExp_expN //; case=> epb.
  rewrite -eXa hmqv_K_sym -epb in eK.
  have [epa [_ [_ eXb]]] := @hmqv_K_inj t_a t_b p_a x_a p_b p_a' x_a p_b
                                        X_b (TExp g x_b') gNX gNm tab eK.
  by do !split => //.
case: (decide (m_b = m_b')) => [emb|neb].
  move: (emb); rewrite /m_b /m_b' => /hmqv_m_inj [] _ [] eXb epa.
  move/(f_equal expo): epa; rewrite !expo_TExp_expN //; case=> epa.
  rewrite eXb hmqv_K_sym epa in eK.
  have [epb [_ [_ eXa]]] := @hmqv_K_inj t_b t_a p_b x_b' p_a' p_b' x_b' p_a'
                                        (TExp g x_a) X_a' gNX gNm tba eK.
  by do !split => //.
have in4 : (0 < gcount (hmqv_ss t_a t_b p_a (TExp g p_a) (TExp g x_a) p_b X_b)
                   (hmqv_K t_b t_a p_b' x_b' (TExp g p_b') (TExp g x_b')
                           (TExp g p_a') X_a'))%Z.
  apply/gcount_gt0; rewrite -eK; apply: hmqv_K_gfactor => //; by right.
have in4' :
    (0 < gcount (hmqv_ss t_b t_a p_b' (TExp g p_b') (TExp g x_b') p_a' X_a')
                (hmqv_K t_a t_b p_a x_a (TExp g p_a) (TExp g x_a)
                        (TExp g p_b) X_b))%Z.
  apply/gcount_gt0; rewrite eK; apply: hmqv_K_gfactor => //; by right.
have ltb : tsize X_b < tsize m_b by exact: tsize_hmqv_m_lt.
have lta' : tsize X_a' < tsize m_a' by exact: tsize_hmqv_m_lt.
case: (decide (tsize X_a' < tsize m_b)) => [lt|nlt].
  have E := @gcount_ss_hmqv_K_cross t_a t_b p_a x_a p_b p_a' x_b' p_b'
                                    X_b X_a' gNX gNm tab nea neb lt.
  by cbv zeta in E; move: in4; rewrite E; lia.
case: (decide (tsize X_b < tsize m_a')) => [lt'|nlt']; last by lia.
have E := @gcount_ss_hmqv_K_cross t_b t_a p_b' x_b' p_a' p_b x_a p_a
                                  X_a' X_b gNX gNm tba
                                  (not_eq_sym neb) (not_eq_sym nea) lt'.
by cbv zeta in E; move: in4'; rewrite E; lia.
Qed.

End HMQV.

Section HMQVIris.

Context `{!cryptisGS Σ, !heapGS Σ}.
Abbreviation iProp := (iProp Σ).

Implicit Types t : term.

Lemma minted_hmqv_m N (t : string) X P :
  minted X -∗ minted P -∗ minted (hmqv_m N t X P).
Proof.
iIntros "#mX #mP"; rewrite /hmqv_m.
iApply minted_THash; iApply minted_tag; iApply minted_of_list => /=.
by do !iSplit => //.
Qed.

Lemma public_hmqv_m N (t : string) X P :
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
    ephemeral: its [exp_pred_base] lets it be used as a DH exponent.  Whether
    it stays secret is up to its owner. *)

Definition hmqv_key (x : nonce) : iProp :=
  minted x ∗ □ (∀ t, exp_pred_base x t ↔ ▷ □ dh_key_share t).

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
by move/(@TExp_injr g _ _ gNm): e => - [] <-.
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
