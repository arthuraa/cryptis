(* TLS 1.3 handshake — executable layer.

   Pure term models + HeapLang implementations (each [Module I]) of every
   protocol component (Meth, CShare, SShare, CParams, SParams), plus the
   top-level [tls_client] / [tls_server] programs.  No Iris proofs live here.
   Dependency-order neighbour: imported by proofs/base.v and every
   proofs/<component>.v. *)

From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib cryptis primitives tactics role.
From cryptis.lib Require Import dh.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**

The key exchange is carried out using one of the following methods:

- [Psk psk]: Exchange of public client and server nonces authenticated with a
  common secret pre-shared key psk.

- [Dh g]: Diffie-Hellman key exchange using [g] as the base group element.

- [PskDh psk g]: A combination of the previous two methods.

Pre-shared keys allow the client to authenticate to the server on the first
flight of messages, and also to send encrypted data before the handshake is
complete.  Diffie-Hellman key exchange is used to provide forward secrecy
guarantees to the session keys.

The [encode] function is used to hash pre-shared keys so that the method can
be sent over the network.

*)

Module Meth.

Variant t :=
| Psk of term
| Dh of term
| PskDh of term & term.

Definition encode N ke :=
  match ke with
  | Psk psk => Psk (THash (Spec.tag (Tag $ N.@"psk") psk))
  | Dh g => Dh g
  | PskDh psk g => PskDh (THash (Spec.tag (Tag $ N.@"psk") psk)) g
  end.

Definition term_of ke :=
  match ke with
  | Psk psk => Spec.tag (Tag $ nroot.@"psk") psk
  | Dh g => Spec.tag (Tag $ nroot.@"dh") g
  | PskDh psk g => Spec.tag (Tag $ nroot.@"pskdh") (Spec.of_list [psk; g])
  end.

Definition of_term ke :=
  if Spec.untag (Tag $ nroot.@"psk") ke is Some args then
    Some (Psk args)
  else if Spec.untag (Tag $ nroot.@"dh") ke is Some args then
    Some (Dh args)
  else if Spec.untag (Tag $ nroot.@"pskdh") ke is Some args then
    args ← Spec.to_list args;
    '(psk, g) ← prod_of_list 2 args;
    Some (PskDh psk g)
  else None.

Lemma term_of_cancel ke : of_term (term_of ke) = Some ke.
Proof.
case: ke => [psk|g|psk g] /=; rewrite /of_term.
- rewrite Spec.tagK //.
- rewrite Spec.untag_tag_ne => [|/Tag_inj c]; last by destruct (ndot_inj _ _ _ _ c).
  rewrite Spec.tagK //.
- rewrite Spec.untag_tag_ne => [|/Tag_inj c]; last by destruct (ndot_inj _ _ _ _ c).
  rewrite Spec.untag_tag_ne => [|/Tag_inj c]; last by destruct (ndot_inj _ _ _ _ c).
  rewrite Spec.tagK Spec.of_listK /=.
  by rewrite unlock /=.
Qed.

#[global]
Instance meth_eqdec : EqDecision t.
Proof.
apply: (inj_eq_dec term_of).
by move=> ?? /(f_equal of_term); rewrite !term_of_cancel; case.
Qed.

#[global]
Instance meth_countable : Countable t.
Proof.
apply (inj_countable term_of of_term).
exact: term_of_cancel.
Qed.

Definition psk ke :=
  match ke with
  | Psk psk => psk
  | Dh _ => Spec.zero
  | PskDh psk _ => psk
  end.

Definition has_dh ke :=
  match ke with Psk _ => false | _ => true end.

Definition has_psk ke :=
  match ke with Dh _ => false | _ => true end.

Definition compatible psk g ke :=
  match ke with
  | Psk psk' => psk' = psk
  | Dh g' => g' = g
  | PskDh psk' g' => psk' = psk ∧ g' = g
  end.

Module I.

Definition Psk : val := (λ: "psk",
  tag (Tag $ nroot.@"psk") "psk"
).

Definition Dh : val := (λ: "g",
  tag (Tag $ nroot.@"dh") "g"
).

Definition PskDh : val := (λ: "psk" "g",
  tag (Tag $ nroot.@"pskdh") (term_of_list ["psk"; "g"])
).

Definition case : val := λ: "ke" "f_psk" "f_dh" "f_pskdh",
  match: untag (Tag $ nroot.@"psk") "ke" with
    SOME "psk" => "f_psk" "psk"
  | NONE =>
  match: untag (Tag $ nroot.@"dh") "ke" with
    SOME "g" => "f_dh" "g"
  | NONE =>
  match: untag (Tag $ nroot.@"pskdh") "ke" with
    SOME "args" =>
    bind: "l" := list_of_term "args" in
    list_match: ["psk"; "g"] := "l" in
    "f_pskdh" "psk" "g"
  | NONE => NONE end end end.

End I.
End Meth.

Coercion Meth.term_of : Meth.t >-> term.

(**

A client share is the choice of a key exchange method together with fresh keying
material determined by the client.  If Diffie-Hellman is used, this keying
material is an exponent [x], and the serialization function simply computes
[g^x].  If Diffie-Hellman is not used, the client simply choses a fresh nonce to
ensure the unicity of session identifiers.  Note that, in this case, the nonce
is public, and is not changed by serialization.

*)

Module CShare.

Variant t :=
| Psk of term & term
| Dh of term & term & term
| PskDh of term & term & term & term.

Definition meth_of ke :=
  match ke with
  | Psk psk _ => Meth.Psk psk
  | Dh g _ _ => Meth.Dh g
  | PskDh psk g _ _ => Meth.PskDh psk g
  end.

Definition has_dh ke := Meth.has_dh (meth_of ke).

Definition has_psk ke := Meth.has_psk (meth_of ke).

Definition encode N ke :=
  match ke with
  | Psk psk cn => Psk (THash (Spec.tag (Tag $ N.@"psk") psk)) cn
  | Dh g cn x => Dh g cn (TExp g x)
  | PskDh psk g cn x => PskDh (THash (Spec.tag (Tag $ N.@"psk") psk)) g cn (TExp g x)
  end.

Definition encode' N ke :=
  match ke with
  | Psk psk cn => Psk (THash (Spec.tag (Tag $ N.@"psk") psk)) cn
  | Dh g cn gx => Dh g cn gx
  | PskDh psk g cn gx => PskDh (THash (Spec.tag (Tag $ N.@"psk") psk)) g cn gx
  end.

Definition term_of ke :=
  match ke with
  | Psk psk cn => Spec.tag (Tag $ nroot.@"psk") (Spec.of_list [psk; cn])
  | Dh g cn x => Spec.tag (Tag $ nroot.@"dh") (Spec.of_list [g; cn; x])
  | PskDh psk g cn x => Spec.tag (Tag $ nroot.@"pskdh") (Spec.of_list [psk; g; cn; x])
  end.

Definition of_term ke :=
  if Spec.untag (Tag $ nroot.@"psk") ke is Some args then
    args ← Spec.to_list args;
    '(psk, cn) ← prod_of_list 2 args;
    Some (Psk psk cn)
  else if Spec.untag (Tag $ nroot.@"dh") ke is Some args then
    args ← Spec.to_list args;
    '(g, cn, gx) ← prod_of_list 3 args;
    Some (Dh g cn gx)
  else if Spec.untag (Tag $ nroot.@"pskdh") ke is Some args then
    args ← Spec.to_list args;
    '(psk, g, cn, gx) ← prod_of_list 4 args;
    Some (PskDh psk g cn gx)
  else None.

Lemma term_ofK ke : of_term (term_of ke) = Some ke.
Proof.
rewrite /of_term.
case: ke => [psk cn|g cn gx|psk g cn gx] /=.
- by rewrite Spec.tagK Spec.of_listK /= unlock /=.
- rewrite Spec.untag_tag_ne //; try set_solver.
  by rewrite Spec.tagK Spec.of_listK /= unlock /=.
- rewrite Spec.untag_tag_ne //; try set_solver.
- rewrite Spec.untag_tag_ne //; try set_solver.
  by rewrite Spec.tagK Spec.of_listK /= unlock /=.
Qed.

Lemma term_of_inj : Inj (=) (=) term_of.
Proof.
move=> ke1 ke2 /(f_equal of_term).
by rewrite !term_ofK; case.
Qed.

Lemma of_termK ke ke' : of_term ke = Some ke' → ke = term_of ke'.
Proof.
rewrite /of_term.
case: Spec.untagP => [ {}ke ->|_] /=.
  case: Spec.to_listP => [ {}ke|//] /=.
  elim/(list_len_rect 2): ke => [psk cn|ke neq]; last first.
    by rewrite prod_of_list_neq.
  by rewrite unlock /= => - [<-].
case: Spec.untagP => [ {}ke ->|_] /=.
  case: Spec.to_listP => [ {}ke|//] /=.
  elim/(list_len_rect 3): ke => [g cn gx|ke neq]; last first.
    by rewrite prod_of_list_neq.
  by rewrite unlock /= => - [<-].
case: Spec.untagP => [ {}ke ->|//].
case: Spec.to_listP => [ {}ke|//] /=.
elim/(list_len_rect 4): ke => [psk g cn gx|ke neq]; last first.
  by rewrite prod_of_list_neq.
by rewrite unlock /= => - [<-].
Qed.

(** The pre-shared key associated with a share.  This is zero if no pre-shared
key is being used. *)

Definition psk ke := Meth.psk (meth_of ke).

Lemma psk_meth_of ke : Meth.psk (meth_of ke) = psk ke.
Proof. by case: ke. Qed.

Definition cnonce ke :=
  match ke with
  | Psk _ cn | Dh _ cn _ | PskDh _ _ cn _ => cn
  end.

(** Check if a client share is compatible with the server parameters psk and g.
If so, return the value of [psk] on that share. *)

Definition check N psk g ke :=
  match ke with
  | Psk psk' cn =>
    if decide (psk' = THash (Spec.tag (Tag $ N.@"psk") psk)) then
      Some (Psk psk cn)
    else None
  | Dh g' cn gx =>
    if decide (g' = g) then Some (Dh g cn gx) else None
  | PskDh psk' g' cn gx =>
    if decide (psk' = THash (Spec.tag (Tag $ N.@"psk") psk) ∧ g' = g) then
      Some (PskDh psk g cn gx)
    else None
  end.

Module I.

Definition case : val := λ: "ke" "f_psk" "f_dh" "f_pskdh",
  match: untag (Tag $ nroot.@"psk") "ke" with
    SOME "args" =>
    bind: "l" := list_of_term "args" in
    list_match: ["psk"; "cn"] := "l" in
    "f_psk" "psk" "cn"
  | NONE =>
  match: untag (Tag $ nroot.@"dh") "ke" with
    SOME "args" =>
    bind: "l" := list_of_term "args" in
    list_match: ["g"; "cn"; "x"] := "l" in
    "f_dh" "g" "cn" "x"
  | NONE =>
  match: untag (Tag $ nroot.@"pskdh") "ke" with
    SOME "args" =>
    bind: "l" := list_of_term "args" in
    list_match: ["psk"; "g"; "cn"; "x"] := "l" in
    "f_pskdh" "psk" "g" "cn" "x"
  | NONE => NONE end end end.

Definition encode N : val := λ: "ke",
  case "ke"
    (λ: "psk" "cn",
      tag (Tag $ nroot.@"psk") (term_of_list [hash (tag (Tag $ N.@"psk") "psk"); "cn"]))
    (λ: "g" "cn" "x",
      let: "gx" := texp "g" "x" in
      tag (Tag $ nroot.@"dh") (term_of_list ["g"; "cn"; "gx"]))
    (λ: "psk" "g" "cn" "x",
      let: "gx" := texp "g" "x" in
      tag (Tag $ nroot.@"pskdh") (term_of_list [hash (tag (Tag $ N.@"psk") "psk"); "g"; "cn"; "gx"])).

Definition psk : val := λ: "ke",
  case "ke"
    (λ: "psk" <>, "psk")
    (λ: <> <> <>, Spec.zero)
    (λ: "psk" <> <> <>, "psk").

Definition of_term : val := λ: "ke",
  match: untag (Tag $ nroot.@"psk") "ke" with SOME "args" =>
    bind: "args" := list_of_term "args" in
    list_match: ["psk"; "cn"] := "args" in
    SOME "ke"
  | NONE =>
  match: untag (Tag $ nroot.@"dh") "ke" with SOME "args" =>
    bind: "args" := list_of_term "args" in
    list_match: ["g"; "cn"; "gx"] := "args" in
    SOME "ke"
  | NONE =>
  match: untag (Tag $ nroot.@"pskdh") "ke" with SOME "args" =>
    bind: "args" := list_of_term "args" in
    list_match: ["psk"; "g"; "cn"; "gx"] := "args" in
    SOME "ke"
  | NONE => NONE
  end end end.

Definition check N : val := λ: "psk" "g" "ke",
  case "ke"
    (λ: "psk'" "cn",
        if: eq_term "psk'" (hash (tag (Tag $ N.@"psk") "psk")) then
          SOME (tag (Tag $ nroot.@"psk") (term_of_list ["psk"; "cn"]))
        else NONE)
    (λ: "g'" "cn" "gx",
        if: eq_term "g'" "g" then
          SOME (tag (Tag $ nroot.@"dh") (term_of_list ["g"; "cn"; "gx"]))
        else NONE)
    (λ: "psk'" "g'" "cn" "gx",
        if: eq_term "psk'" (hash (tag (Tag $ N.@"psk") "psk")) &&
            eq_term "g'" "g" then
          SOME (tag (Tag $ nroot.@"pskdh") (term_of_list ["psk"; "g"; "cn"; "gx"]))
        else NONE).

Definition new : val := λ: "ke",
  Meth.I.case "ke"
    (λ: "psk",
      tag (Tag $ nroot.@"psk") (term_of_list ["psk"; mk_nonce #()]))
    (λ: "g",
      tag (Tag $ nroot.@"dh") (term_of_list ["g"; mk_nonce #(); mk_dh #()]))
    (λ: "psk" "g",
      tag (Tag $ nroot.@"pskdh") (term_of_list ["psk"; "g"; mk_nonce #(); mk_dh #()])).

End I.
End CShare.

Coercion CShare.term_of : CShare.t >-> term.

Module SShare.

Variant t :=
| Psk of term & term & term
| Dh of term & term & term & term & term
| PskDh of term & term & term & term & term & term.

Definition encode N ke :=
  match ke with
  | Psk psk cn sn =>
    Psk (THash (Spec.tag (Tag $ N.@"psk") psk)) cn sn
  | Dh g cn sn gx y =>
    Dh g cn sn gx (TExp g y)
  | PskDh psk g cn sn gx y =>
    PskDh (THash (Spec.tag (Tag $ N.@"psk") psk)) g cn sn gx (TExp g y)
  end.

Definition encode' N ke :=
  match ke with
  | Psk psk cn sn =>
    Psk (THash (Spec.tag (Tag $ N.@"psk") psk)) cn sn
  | Dh g cn sn x gy =>
    Dh g cn sn (TExp g x) gy
  | PskDh psk g cn sn x gy =>
    PskDh (THash (Spec.tag (Tag $ N.@"psk") psk)) g cn sn (TExp g x) gy
  end.

Definition term_of ke :=
  match ke with
  | Psk psk cn sn =>
    Spec.tag (Tag $ nroot.@"psk") (Spec.of_list [psk; cn; sn])
  | Dh g cn sn x y =>
    Spec.tag (Tag $ nroot.@"dh") (Spec.of_list [g; cn; sn; x; y])
  | PskDh psk g cn sn x y =>
    Spec.tag (Tag $ nroot.@"pskdh") (Spec.of_list [psk; g; cn; sn; x; y])
  end.

Lemma term_of_inj : Inj (=) (=) term_of.
Proof.
move=> ke1 ke2; case: ke1 =>>; case: ke2 =>> /= /Spec.tag_inj [/Tag_inj e];
case: (ndot_inj _ _ _ _ e) => // _ _.
- by case/Spec.of_list_inj => -> -> ->.
- by case/Spec.of_list_inj => -> -> -> -> ->.
- by case/Spec.of_list_inj => -> -> -> -> -> ->.
Qed.

Definition cshare_of ke :=
  match ke with
  | Psk psk cn sn => CShare.Psk psk cn
  | Dh g cn sn x y => CShare.Dh g cn x
  | PskDh psk g cn sn x y => CShare.PskDh psk g cn x
  end.

Definition meth_of ke := CShare.meth_of (cshare_of ke).

Definition has_psk ke := CShare.has_psk (cshare_of ke).

Definition has_dh ke := CShare.has_dh (cshare_of ke).

Definition cnonce ke :=
  match ke with
  | Psk _ cn _ | Dh _ cn _ _ _ | PskDh _ _ cn _ _ _ => cn
  end.

Lemma cnonce_cshare_of kex :
  CShare.cnonce (cshare_of kex) = cnonce kex.
Proof. by case: kex. Qed.

Definition snonce ke :=
  match ke with
  | Psk _ _ sn | Dh _ _ sn _ _ | PskDh _ _ _ sn _ _ => sn
  end.

Lemma cnonce_encode N ke : cnonce (encode N ke) = cnonce ke.
Proof. by case: ke. Qed.

Lemma snonce_encode N ke : snonce (encode N ke) = snonce ke.
Proof. by case: ke. Qed.

Lemma cnonce_encode' N ke : cnonce (encode' N ke) = cnonce ke.
Proof. by case: ke. Qed.

Lemma snonce_encode' N ke : snonce (encode' N ke) = snonce ke.
Proof. by case: ke. Qed.

Definition psk ke := CShare.psk (cshare_of ke).

(** Compute the session key given the pre-shared key used by the server and its
key share. *)

Definition session_key_of ke :=
  SEncKey match ke with
  | Psk psk cn sn => Spec.of_list [psk; cn; sn]
  | Dh _ _ _ gx y => TExp gx y
  | PskDh psk _ _ _ gx y => Spec.of_list [psk; TExp gx y]
  end.

(** Similar to the above, but should be called by the client *)

Definition session_key_of' ke :=
  match ke with
  | Psk psk cn sn => SEncKey (Spec.of_list [psk; cn; sn])
  | Dh _ _ _ x gy => SEncKey (TExp gy x)
  | PskDh psk _ _ _ x gy => SEncKey (Spec.of_list [psk; TExp gy x])
  end.

Lemma encode_eq N kex1 kex2 :
  encode' N kex1 = encode N kex2 →
  cnonce kex1 = cnonce kex2 ∧
  snonce kex1 = snonce kex2 ∧
  session_key_of' kex1 = session_key_of kex2 ∧
  has_dh kex1 = has_dh kex2 ∧
  psk kex1 = psk kex2 ∧
  meth_of kex1 = meth_of kex2.
Proof.
rewrite /session_key_of.
case: kex1 kex2 => [???|?????|??????] [???|?????|??????] //=.
- by case=> [/Spec.tag_inj [_ ->] -> ->].
- by case=> e_g -> -> <- ->; rewrite e_g TExpC.
- by case=> [] /Spec.tag_inj [_ ->] e_g -> -> <- ->; rewrite e_g TExpC.
Qed.

(** Check a server share against a corresponding client share.  This function
should be used by the client, so the server share is encoded as a term. If the
check succeeds, return the corresponding session key; otherwise, return None. *)

Definition check N c_kex ke :=
  match c_kex with
  | CShare.Psk psk cn =>
    s_kex ← Spec.untag (Tag $ nroot.@"psk") ke;
    s_kex ← Spec.to_list s_kex;
    '(psk', cn', sn) ← prod_of_list 3 s_kex;
    if decide (psk' = THash (Spec.tag (Tag $ N.@"psk") psk) ∧ cn' = cn) then
      Some (Psk psk cn sn)
    else None
  | CShare.Dh g cn x =>
    s_kex ← Spec.untag (Tag $ nroot.@"dh") ke;
    s_kex ← Spec.to_list s_kex;
    '(g', cn', sn, gx, gy) ← prod_of_list 5 s_kex;
    if decide (g' = g ∧ cn' = cn ∧ gx = TExp g x) then
      let skey := SEncKey (TExp gy x) in
      Some (Dh g cn sn x gy)
    else None
  | CShare.PskDh psk g cn x =>
    s_kex ← Spec.untag (Tag $ nroot.@"pskdh") ke;
    s_kex ← Spec.to_list s_kex;
    '(psk', g', cn', sn, gx, gy) ← prod_of_list 6 s_kex;
    if decide (psk' = THash (Spec.tag (Tag $ N.@"psk") psk)
               ∧ g' = g ∧ cn' = cn ∧ gx = TExp g x) then
      let skey := SEncKey (TExp gy x) in
      Some (PskDh psk g cn sn x gy)
    else None
  end.

Module I.

Definition case : val := λ: "ke" "f_psk" "f_dh" "f_pskdh",
  match: untag (Tag $ nroot.@"psk") "ke" with
    SOME "args" =>
    bind: "l" := list_of_term "args" in
    list_match: ["psk"; "cn"; "sn"] := "l" in
    "f_psk" "psk" "cn" "sn"
  | NONE =>
  match: untag (Tag $ nroot.@"dh") "ke" with
    SOME "args" =>
    bind: "l" := list_of_term "args" in
    list_match: ["g"; "cn"; "sn"; "x"; "y"] := "l" in
    "f_dh" "g" "cn" "sn" "x" "y"
  | NONE =>
  match: untag (Tag $ nroot.@"pskdh") "ke" with
    SOME "args" =>
    bind: "l" := list_of_term "args" in
    list_match: ["psk"; "g"; "cn"; "sn"; "x"; "y"] := "l" in
    "f_pskdh" "psk" "g" "cn" "sn" "x" "y"
  | NONE => NONE end end end.

Definition cnonce : val := λ: "ke",
  case "ke"
    (λ: <> "cn" <>, "cn")
    (λ: <> "cn" <> <> <>, "cn")
    (λ: <> <> "cn" <> <> <>, "cn").

Definition snonce : val := λ: "ke",
  case "ke"
    (λ: <> <> "sn", "sn")
    (λ: <> <> "sn" <> <>, "sn")
    (λ: <> <> <> "sn" <> <>, "sn").

Definition encode N : val := λ: "ke",
  case "ke"
    (λ: "psk" "cn" "sn",
      let: "psk" := hash (tag (Tag $ N.@"psk") "psk") in
      tag (Tag $ nroot.@"psk") (term_of_list ["psk"; "cn"; "sn"]))
    (λ: "g" "cn" "sn" "gx" "y",
      let: "gy" := texp "g" "y" in
      tag (Tag $ nroot.@"dh") (term_of_list ["g"; "cn"; "sn"; "gx"; "gy"]))
    (λ: "psk" "g" "cn" "sn" "gx" "y",
      let: "psk" := hash (tag (Tag $ N.@"psk") "psk") in
      let: "gy" := texp "g" "y" in
      tag (Tag $ nroot.@"pskdh") (term_of_list ["psk"; "g"; "cn"; "sn"; "gx"; "gy"])).

Definition session_key_of : val := λ: "ke",
  case "ke"
    (λ: "psk" "c_nonce" "s_nonce",
       derive_senc_key (term_of_list ["psk"; "c_nonce"; "s_nonce"]))
    (λ: <> <> <> "gx" "y", derive_senc_key (texp "gx" "y"))
    (λ: "psk" <> <> <> "gx" "y",
       derive_senc_key (term_of_list ["psk"; texp "gx" "y"])).

Definition session_key_of' : val := λ: "ke",
  case "ke"
    (λ: "psk" "c_nonce" "s_nonce",
       derive_senc_key (term_of_list ["psk"; "c_nonce"; "s_nonce"]))
    (λ: <> <> <> "x" "gy", derive_senc_key (texp "gy" "x"))
    (λ: "psk" <> <> <> "x" "gy",
       derive_senc_key (term_of_list ["psk"; texp "gy" "x"])).

Definition check N : val := λ: "c_kex" "s_kex",
  CShare.I.case "c_kex"
    (λ: "psk" "cn",
      bind: "s_kex" := untag (Tag $ nroot.@"psk") "s_kex" in
      bind: "s_kex" := list_of_term "s_kex" in
      list_match: ["psk'"; "cn'"; "sn"] := "s_kex" in
      if: eq_term "psk'" (hash (tag (Tag $ N.@"psk") "psk"))
          && eq_term "cn'" "cn" then
        SOME (tag (Tag $ nroot.@"psk") (term_of_list ["psk"; "cn"; "sn"]))
      else NONE)
    (λ: "g" "cn" "x",
      bind: "s_kex" := untag (Tag $ nroot.@"dh") "s_kex" in
      bind: "s_kex" := list_of_term "s_kex" in
      list_match: ["g'"; "cn'"; "sn"; "gx"; "gy"] := "s_kex" in
      if: eq_term "g'" "g" && eq_term "cn'" "cn" &&
          eq_term "gx" (texp "g" "x") then
        SOME (tag (Tag $ nroot.@"dh") (term_of_list ["g"; "cn"; "sn"; "x"; "gy"]))
      else NONE)
    (λ: "psk" "g" "cn" "x",
      bind: "s_kex" := untag (Tag $ nroot.@"pskdh") "s_kex" in
      bind: "s_kex" := list_of_term "s_kex" in
      list_match: ["psk'"; "g'"; "cn'"; "sn"; "gx"; "gy"] := "s_kex" in
      if: eq_term "psk'" (hash (tag (Tag $ N.@"psk") "psk")) &&
          eq_term "g'" "g" && eq_term "cn'" "cn" &&
          eq_term "gx" (texp "g" "x") then
        SOME (tag (Tag $ nroot.@"pskdh") (term_of_list ["psk"; "g"; "cn"; "sn"; "x"; "gy"]))
      else NONE).

Definition new : val := λ: "ke",
  CShare.I.case "ke"
    (λ: "psk" "c_nonce",
        tag (Tag $ nroot.@"psk") (term_of_list ["psk"; "c_nonce"; mk_nonce #()]))
    (λ: "g" "cn" "gx",
      tag (Tag $ nroot.@"dh") (term_of_list ["g"; "cn"; mk_nonce #(); "gx"; mk_dh #()]))
    (λ: "psk" "g" "cn" "gx",
      tag (Tag $ nroot.@"pskdh") (term_of_list ["psk"; "g"; "cn"; mk_nonce #(); "gx"; mk_dh #()])).

End I.
End SShare.

Coercion SShare.term_of : SShare.t >-> term.

Module CParams.

Record t := Params {
  share : CShare.t;
  other : term;
}.

Definition encode N cp :=
  {| share := CShare.encode N (share cp);
     other := other cp |}.

Definition term_of cp :=
  Spec.of_list [CShare.term_of (share cp); other cp].

Definition hello_pub N cp :=
  term_of (encode N cp).

Definition hello_mac N cp :=
  let ch := hello_pub N cp in
  let psk := CShare.psk (share cp) in
  THash (Spec.tag (Tag $ N.@"binder") (Spec.of_list [psk; ch])).

Definition hello N cp :=
  Spec.of_list [
    hello_pub N cp;
    hello_mac N cp
  ].

Definition check N psk g (other : term) ch :=
  ch ← Spec.to_list ch;
  '(ch, mac) ← prod_of_list 2 ch;
  ch' ← Spec.to_list ch;
  '(ke, other') ← prod_of_list 2 ch';
  ke ← CShare.of_term ke;
  ke ← CShare.check N psk g ke;
  let psk := CShare.psk ke in
  let mac' := THash (Spec.tag (Tag $ N.@"binder") (Spec.of_list [psk; ch])) in
  if decide (other' = other ∧ mac' = mac) then Some ke else None.

Module I.

Definition hello N : val := λ: "cp",
  bind: "cp" := list_of_term "cp" in
  list_match: ["kex"; "other"] := "cp" in
  let: "ts" := term_of_list [CShare.I.encode N "kex"; "other"] in
  let: "psk" := CShare.I.psk "kex" in
  let: "mac" := hash (tag (Tag $ N.@"binder") (term_of_list ["psk"; "ts"])) in
  term_of_list ["ts"; "mac"].

Definition check N : val := λ: "psk" "g" "other" "ch",
  bind: "ch" := list_of_term "ch" in
  list_match: ["ch"; "mac"] := "ch" in
  bind: "ch'" := list_of_term "ch" in
  list_match: ["ke"; "other'"] := "ch'" in
  bind: "ke" := CShare.I.of_term "ke" in
  bind: "ke" := CShare.I.check N "psk" "g" "ke" in
  let: "psk" := CShare.I.psk "ke" in
  let: "mac'" := hash (tag (Tag $ N.@"binder") (term_of_list ["psk"; "ch"])) in
  if: eq_term "other'" "other" && eq_term "mac'" "mac" then SOME "ke" else NONE.

End I.
End CParams.

Coercion CParams.term_of : CParams.t >-> term.

Module SParams.

Record t := Params {
  share : SShare.t;
  verif_key : sign_key;
  other : term;
}.

Definition encode N sp :=
  {| share := SShare.encode N (share sp);
     verif_key := verif_key sp;
     other := other sp |}.

Definition term_of sp :=
  Spec.of_list [
    SShare.term_of (share sp);
    verif_key sp : term;
    other sp
  ].

Definition hello_pub N sp :=
  Spec.of_list [
    SShare.term_of (SShare.encode N (share sp));
    other sp
  ].

Definition hello_priv N sp :=
  let pub := hello_pub N sp in
  Spec.of_list [
    Spec.pkey (verif_key sp);
    TSeal (verif_key sp) (Spec.tag (Tag $ N.@"server_hello_sig") (THash pub))
  ].

Definition hello N sp :=
  let pub := hello_pub N sp in
  let enc := hello_priv N sp in
  let session_key := SShare.session_key_of (share sp) in
  Spec.of_list [
    pub;
    TSeal session_key (Spec.tag (Tag $ N.@"server_hello") enc)
  ].

Definition verify k N x sig :=
  match Spec.dec k N sig with
  | Some y => bool_decide (y = THash x)
  | None => false
  end.

Definition check N cp sp :=
  sp ← Spec.to_list sp;
  '(pub, sig) ← prod_of_list 2 sp;
  pub' ← Spec.to_list pub;
  '(kex, other') ← prod_of_list 2 pub';
  res ← SShare.check N (CParams.share cp) kex;
  let session_key := SShare.session_key_of' res in
  dec_sig ← Spec.dec session_key (Tag $ N.@"server_hello") sig;
  dec_sig ← Spec.to_list dec_sig;
  '(verif_key, sig) ← prod_of_list 2 dec_sig;
  if Spec.has_key_type Verify verif_key then
    if decide (other' = CParams.other cp) then
      if verify verif_key (Tag $ N.@"server_hello_sig") pub sig then
        Some (verif_key, res)
      else None
    else None
  else None.

Module I.

Definition case : val := λ: "sp" "f",
  bind: "sp'" := list_of_term "sp" in
  list_match: ["kex"; "verif_key"; "other"] := "sp'" in
  "f" "kex" "verif_key" "other".

Definition hello_pub N : val := λ: "sp",
  case "sp" (λ: "kex" "verif_key" "other",
    term_of_list [SShare.I.encode N "kex"; "other"]).

Definition hello N : val := λ: "sp",
  case "sp" (λ: "kex" "verif_key" "other",
    let: "pub" := hello_pub N "sp" in
    let: "enc" := sign "verif_key" (Tag $ N.@"server_hello_sig") (hash "pub") in
    let: "enc" := term_of_list [pkey "verif_key"; "enc"] in
    let: "session_key" := SShare.I.session_key_of "kex" in
    let: "enc" := senc "session_key" (Tag $ N.@"server_hello") "enc" in
    term_of_list ["pub"; "enc"]
  ).

Definition verify : val := λ: "k" "N" "x" "sig",
  match: simple.verify "k" "N" "sig" with
    SOME "y" => eq_term "y" (hash "x")
  | NONE => #false
  end.

Definition check N : val := λ: "cp" "sh",
  bind: "cp" := list_of_term "cp" in
  list_match: ["c_kex"; "c_other"] := "cp" in
  bind: "sh" := list_of_term "sh" in
  list_match: ["pub"; "sig"] := "sh" in
  bind: "pub'" := list_of_term "pub" in
  list_match: ["s_kex"; "s_other"] := "pub'" in
  bind: "res" := SShare.I.check N "c_kex" "s_kex" in
  let: "session_key" := SShare.I.session_key_of' "res" in
  bind: "dec_sig" := sdec "session_key" (Tag $ N.@"server_hello") "sig" in
  bind: "dec_sig" := list_of_term "dec_sig" in
  list_match: ["verif_key"; "sig"] := "dec_sig" in
  guard: is_verify_key "verif_key" in
  if: eq_term "s_other" "c_other" then
    if: verify "verif_key" (Tag $ N.@"server_hello_sig") "pub" "sig" then
      SOME ("verif_key", "res")
    else NONE
  else NONE.

End I.
End SParams.

Coercion SParams.term_of : SParams.t >-> term.
