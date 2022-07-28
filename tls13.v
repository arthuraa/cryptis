From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics nown.
From cryptis Require Import role session dh.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Keys.

Section Keys.

Context `{!heapGS Σ, cryptisG Σ}.
Notation iProp := (iProp Σ).

Implicit Types t : term.
Implicit Types Φ : val → iProp.

Definition ctx N : iProp :=
  hash_pred (N.@"psk") (λ _, True)%I ∧
  key_pred (N.@"sess_key") (λ _ _, False)%I.

Global Instance ctx_persistent N : Persistent (ctx N).
Proof. apply _. Qed.

Lemma ctx_alloc N E1 E2 E' :
  ↑N.@"psk" ⊆ E1 →
  ↑N.@"sess_key" ⊆ E2 →
  hash_pred_token E1 -∗
  key_pred_token E2 ={E'}=∗
  ctx N ∗
  hash_pred_token (E1 ∖ ↑N.@"psk") ∗
  key_pred_token (E2 ∖ ↑N.@"sess_key").
Proof.
iIntros (??) "tok1 tok2".
iMod (hash_pred_set (N.@"psk") (λ _, True)%I with "tok1")
  as "[? ?]"; eauto.
iFrame.
iMod (key_pred_set (N.@"sess_key") (λ _ _, False)%I with "tok2")
  as "[? ?]"; eauto.
Qed.

End Keys.

End Keys.

#[global]
Existing Instance Keys.ctx_persistent.

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
  | Psk psk => Psk (THash (Spec.tag (N.@"psk") psk))
  | Dh g => Dh g
  | PskDh psk g => PskDh (THash (Spec.tag (N.@"psk") psk)) g
  end.

Definition term_of ke :=
  match ke with
  | Psk psk => Spec.tag (nroot.@"psk") psk
  | Dh g => Spec.tag (nroot.@"dh") g
  | PskDh psk g => Spec.tag (nroot.@"pskdh") (Spec.of_list [psk; g])
  end.

Definition of_term ke :=
  if Spec.untag (nroot.@"psk") ke is Some args then
    Some (Psk args)
  else if Spec.untag (nroot.@"dh") ke is Some args then
    Some (Dh args)
  else if Spec.untag (nroot.@"pskdh") ke is Some args then
    args ← Spec.to_list args;
    '(psk, g) ← prod_of_list 2 args;
    Some (PskDh psk g)
  else None.

Lemma term_of_cancel ke : of_term (term_of ke) = Some ke.
Proof.
case: ke => [psk|g|psk g] /=; rewrite /of_term.
- rewrite Spec.tagK //.
- rewrite Spec.untag_tag_ne => [|c]; last by destruct (ndot_inj _ _ _ _ c).
  rewrite Spec.tagK //.
- rewrite Spec.untag_tag_ne => [|c]; last by destruct (ndot_inj _ _ _ _ c).
  rewrite Spec.untag_tag_ne => [|c]; last by destruct (ndot_inj _ _ _ _ c).
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
  tag (nroot.@"psk") "psk"
).

Definition Dh : val := (λ: "g",
  tag (nroot.@"dh") "g"
).

Definition PskDh : val := (λ: "psk" "g",
  tag (nroot.@"pskdh") (term_of_list ["psk"; "g"])
).

Definition case : val := λ: "ke" "f_psk" "f_dh" "f_pskdh",
  match: untag (nroot.@"psk") "ke" with
    SOME "psk" => "f_psk" "psk"
  | NONE =>
  match: untag (nroot.@"dh") "ke" with
    SOME "g" => "f_dh" "g"
  | NONE =>
  match: untag (nroot.@"pskdh") "ke" with
    SOME "args" =>
    bind: "l" := list_of_term "args" in
    list_match: ["psk"; "g"] := "l" in
    "f_pskdh" "psk" "g"
  | NONE => NONE end end end.

End I.

Section Proofs.

Context `{!heapGS Σ, cryptisG Σ}.
Notation iProp := (iProp Σ).

Implicit Types t : term.

Lemma wp_Psk t E :
  {{{ True }}} I.Psk t @ E {{{ (v : val), RET v; ⌜v = term_of (Psk t)⌝ }}}.
Proof.
iIntros "%Φ _ post"; rewrite /I.Psk.
by wp_pures; wp_tag; iApply "post".
Qed.

Lemma wp_Dh t E :
  {{{ True }}} I.Dh t @ E {{{ (v : val), RET v; ⌜v = term_of (Dh t)⌝ }}}.
Proof.
iIntros "%Φ _ post"; rewrite /I.Dh.
by wp_pures; wp_tag; iApply "post".
Qed.

Lemma wp_PskDh t1 t2 E :
  {{{ True }}} I.PskDh t1 t2 @ E
  {{{ (v : val), RET v; ⌜v = term_of (PskDh t1 t2)⌝ }}}.
Proof.
iIntros "%Φ _ post"; rewrite /I.PskDh.
by wp_pures; wp_list; wp_term_of_list; wp_tag; iApply "post".
Qed.

Lemma wp_case ke (f_psk f_dh f_pskdh : val) E Φ :
  match ke with
  | Psk psk => WP f_psk psk @ E {{ Φ }}
  | Dh g => WP f_dh g @ E {{ Φ }}
  | PskDh psk g => WP f_pskdh psk g @ E {{ Φ }}
  end -∗
  WP I.case (term_of ke) f_psk f_dh f_pskdh @ E {{ Φ }}.
Proof.
iIntros "post"; rewrite /I.case.
wp_untag_eq psk e_psk.
  case: ke e_psk => [?|?|??] /= /Spec.tag_inj []; try set_solver.
  by move=> _ <-; wp_pures.
wp_untag_eq args e_dh.
  case: ke e_psk e_dh => [?|?|??] /= e_psk /Spec.tag_inj []; try set_solver.
  by move=> _ <- {e_psk args}; wp_pures.
wp_untag_eq args e_pskdh; last first.
  by case: ke e_psk e_dh e_pskdh =>> /=; rewrite Spec.tagK.
case: ke e_psk e_dh e_pskdh
  => [?|?|psk g] /= e_psk e_dh /Spec.tag_inj []; try set_solver.
move=> _ <- {e_psk e_dh args}; wp_pures; do !rewrite subst_list_match /=.
wp_list_of_term_eq l e_l; last by rewrite Spec.of_listK in e_l.
move/Spec.of_list_inj: e_l => {l} <-.
by wp_list_match => // _ _ [<- <-].
Qed.

Definition wf ke : iProp :=
  match ke with
  | Psk psk => sterm psk
  | Dh g => pterm g
  | PskDh psk g => sterm psk ∧ pterm g
  end.

#[global]
Instance Persistent_wf ke : Persistent (wf ke).
Proof. by case: ke => *; apply _. Qed.

Lemma pterm_encode N ke :
  Keys.ctx N -∗
  wf ke -∗
  pterm (term_of (encode N ke)).
Proof.
iIntros "#(hash & _ ) #p_ke"; case: ke => [psk|g|psk g] /=.
- rewrite pterm_tag pterm_THash sterm_tag.
  iRight; iSplit => //.
  by iExists _; eauto.
- by rewrite pterm_tag.
- iDestruct "p_ke" as "(s_psk & p_g)".
  rewrite !pterm_tag pterm_of_list /= pterm_THash sterm_tag.
  do !iSplit => //=.
  iRight; iSplit => //.
  by iExists _; eauto.
Qed.

End Proofs.

End Meth.

Coercion Meth.term_of : Meth.t >-> term.
#[global]
Existing Instance Meth.Persistent_wf.

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
  | Psk psk cn => Psk (THash (Spec.tag (N.@"psk") psk)) cn
  | Dh g cn x => Dh g cn (TExp g [x])
  | PskDh psk g cn x => PskDh (THash (Spec.tag (N.@"psk") psk)) g cn (TExp g [x])
  end.

Definition encode' N ke :=
  match ke with
  | Psk psk cn => Psk (THash (Spec.tag (N.@"psk") psk)) cn
  | Dh g cn gx => Dh g cn gx
  | PskDh psk g cn gx => PskDh (THash (Spec.tag (N.@"psk") psk)) g cn gx
  end.

Definition term_of ke :=
  match ke with
  | Psk psk cn => Spec.tag (nroot.@"psk") (Spec.of_list [psk; cn])
  | Dh g cn x => Spec.tag (nroot.@"dh") (Spec.of_list [g; cn; x])
  | PskDh psk g cn x => Spec.tag (nroot.@"pskdh") (Spec.of_list [psk; g; cn; x])
  end.

Definition of_term ke :=
  if Spec.untag (nroot.@"psk") ke is Some args then
    args ← Spec.to_list args;
    '(psk, cn) ← prod_of_list 2 args;
    Some (Psk psk cn)
  else if Spec.untag (nroot.@"dh") ke is Some args then
    args ← Spec.to_list args;
    '(g, cn, gx) ← prod_of_list 3 args;
    Some (Dh g cn gx)
  else if Spec.untag (nroot.@"pskdh") ke is Some args then
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
    if decide (psk' = THash (Spec.tag (N.@"psk") psk)) then
      Some (Psk psk cn)
    else None
  | Dh g' cn gx =>
    if decide (g' = g) then Some (Dh g cn gx) else None
  | PskDh psk' g' cn gx =>
    if decide (psk' = THash (Spec.tag (N.@"psk") psk) ∧ g' = g) then
      Some (PskDh psk g cn gx)
    else None
  end.

Module I.

Definition case : val := λ: "ke" "f_psk" "f_dh" "f_pskdh",
  match: untag (nroot.@"psk") "ke" with
    SOME "args" =>
    bind: "l" := list_of_term "args" in
    list_match: ["psk"; "cn"] := "l" in
    "f_psk" "psk" "cn"
  | NONE =>
  match: untag (nroot.@"dh") "ke" with
    SOME "args" =>
    bind: "l" := list_of_term "args" in
    list_match: ["g"; "cn"; "x"] := "l" in
    "f_dh" "g" "cn" "x"
  | NONE =>
  match: untag (nroot.@"pskdh") "ke" with
    SOME "args" =>
    bind: "l" := list_of_term "args" in
    list_match: ["psk"; "g"; "cn"; "x"] := "l" in
    "f_pskdh" "psk" "g" "cn" "x"
  | NONE => NONE end end end.

Definition encode N : val := λ: "ke",
  case "ke"
    (λ: "psk" "cn",
      tag (nroot.@"psk") (term_of_list [hash (tag (N.@"psk") "psk"); "cn"]))
    (λ: "g" "cn" "x",
      let: "gx" := texp (tgroup "g") "x" in
      tag (nroot.@"dh") (term_of_list ["g"; "cn"; "gx"]))
    (λ: "psk" "g" "cn" "x",
      let: "gx" := texp (tgroup "g") "x" in
      tag (nroot.@"pskdh") (term_of_list [hash (tag (N.@"psk") "psk"); "g"; "cn"; "gx"])).

Definition psk : val := λ: "ke",
  case "ke"
    (λ: "psk" <>, "psk")
    (λ: <> <> <>, Spec.zero)
    (λ: "psk" <> <> <>, "psk").

Definition of_term : val := λ: "ke",
  match: untag (nroot.@"psk") "ke" with SOME "args" =>
    bind: "args" := list_of_term "args" in
    list_match: ["psk"; "cn"] := "args" in
    SOME "ke"
  | NONE =>
  match: untag (nroot.@"dh") "ke" with SOME "args" =>
    bind: "args" := list_of_term "args" in
    list_match: ["g"; "cn"; "gx"] := "args" in
    SOME "ke"
  | NONE =>
  match: untag (nroot.@"pskdh") "ke" with SOME "args" =>
    bind: "args" := list_of_term "args" in
    list_match: ["psk"; "g"; "cn"; "gx"] := "args" in
    SOME "ke"
  | NONE => NONE
  end end end.

Definition check N : val := λ: "psk" "g" "ke",
  case "ke"
    (λ: "psk'" "cn",
        if: eq_term "psk'" (hash (tag (N.@"psk") "psk")) then
          SOME (tag (nroot.@"psk") (term_of_list ["psk"; "cn"]))
        else NONE)
    (λ: "g'" "cn" "gx",
        if: eq_term "g'" "g" then
          SOME (tag (nroot.@"dh") (term_of_list ["g"; "cn"; "gx"]))
        else NONE)
    (λ: "psk'" "g'" "cn" "gx",
        if: eq_term "psk'" (hash (tag (N.@"psk") "psk")) &&
            eq_term "g'" "g" then
          SOME (tag (nroot.@"pskdh") (term_of_list ["psk"; "g"; "cn"; "gx"]))
        else NONE).

Definition new : val := λ: "ke",
  Meth.I.case "ke"
    (λ: "psk",
      tag (nroot.@"psk") (term_of_list ["psk"; mknonce #()]))
    (λ: "g",
      tag (nroot.@"dh") (term_of_list ["g"; mknonce #(); mkdh #()]))
    (λ: "psk" "g",
      tag (nroot.@"pskdh") (term_of_list ["psk"; "g"; mknonce #(); mkdh #()])).

End I.

Section Proofs.

Context `{!heapGS Σ, cryptisG Σ}.
Notation iProp := (iProp Σ).

Implicit Types t : term.
Implicit Types Φ : val → iProp.

Lemma wp_case ke (f_psk f_dh f_pskdh : val) E Φ :
  match ke with
  | Psk psk cn => WP f_psk psk cn @ E {{ Φ }}
  | Dh g cn x => WP f_dh g cn x @ E {{ Φ }}
  | PskDh psk g cn x => WP f_pskdh psk g cn x @ E {{ Φ }}
  end -∗
  WP I.case (term_of ke) f_psk f_dh f_pskdh @ E {{ Φ }}.
Proof.
iIntros "post"; rewrite /I.case.
wp_untag_eq psk e_psk.
  case: ke e_psk => [??|???|????] /= /Spec.tag_inj []; try set_solver.
  move=> _ <-; wp_pures; do !rewrite subst_list_match /=.
  wp_list_of_term_eq l e_l; last by rewrite Spec.of_listK in e_l.
  move/Spec.of_list_inj: e_l => {l} <-.
  by wp_list_match => // _ _ [<- <-].
wp_untag_eq args e_dh.
  case: ke e_psk e_dh => [??|g cn x|????] /= e_psk /Spec.tag_inj []; try set_solver.
  move=> _ <- {e_psk args}; wp_pures; do !rewrite subst_list_match /=.
  wp_list_of_term_eq l e_l; last by rewrite Spec.of_listK in e_l.
  move/Spec.of_list_inj: e_l => {l} <-.
  by wp_list_match => // _ _ _ [<- <- <-].
wp_untag_eq args e_pskdh; last first.
  by case: ke e_psk e_dh e_pskdh =>> /=; rewrite Spec.tagK.
case: ke e_psk e_dh e_pskdh
  => [??|???|psk g cn x] /= e_psk e_dh /Spec.tag_inj []; try set_solver.
move=> _ <- {e_psk e_dh args}; wp_pures; do !rewrite subst_list_match /=.
wp_list_of_term_eq l e_l; last by rewrite Spec.of_listK in e_l.
move/Spec.of_list_inj: e_l => {l} <-.
by wp_list_match => // _ _ _ _ [<- <- <- <-].
Qed.

Lemma wp_encode N ke E Φ :
  Φ (term_of (encode N ke)) -∗
  WP I.encode N (term_of ke) @ E {{ Φ }}.
Proof.
iIntros "post"; rewrite /I.encode; wp_pures.
iApply wp_case.
case: ke => [psk c_nonce|g cn x|psk g cn x] /=; wp_pures.
- by wp_list; wp_tag; wp_hash; wp_list; wp_term_of_list; wp_tag.
- wp_bind (tgroup _); iApply wp_tgroup.
  wp_bind (texp _ _); iApply wp_texp; wp_pures.
  rewrite Spec.texpA.
  wp_list; wp_term_of_list.
  by iApply wp_tag.
- wp_bind (tgroup _); iApply wp_tgroup.
  wp_bind (texp _ _); iApply wp_texp; wp_pures.
  rewrite Spec.texpA.
  wp_list; wp_tag; wp_hash; wp_list; wp_term_of_list.
  by iApply wp_tag.
Qed.

Lemma wp_psk ke E Φ :
  Φ (psk ke) -∗
  WP I.psk (term_of ke) @ E {{ Φ }}.
Proof.
iIntros "post"; rewrite /I.psk; wp_pures.
iApply wp_case.
by case: ke => [psk ?|? ? ?|psk ? ? ?]; wp_pures.
Qed.

Lemma wp_of_term ke E Φ :
  Φ (repr (term_of <$> of_term ke)) -∗
  WP I.of_term ke @ E {{ Φ }}.
Proof.
iIntros "?"; rewrite /term_of /of_term.
rewrite /I.of_term /=; wp_pures.
wp_untag_eq args e; wp_pures.
  rewrite {}e Spec.tagK /=.
  wp_list_of_term_eq args' e; wp_pures; last by rewrite e.
  rewrite {}e Spec.of_listK /=.
  wp_list_match => [?? -> {args'} | neq]; wp_finish; last first.
    by rewrite prod_of_list_neq.
  by rewrite unlock /=; wp_pures.
rewrite {}e.
wp_untag_eq args e; wp_pures.
  rewrite {}e Spec.tagK /=.
  wp_list_of_term_eq args' e; wp_pures; last by rewrite e.
  rewrite {}e Spec.of_listK /=.
  wp_list_match => [??? -> {args'} | neq]; wp_finish; last first.
    by rewrite prod_of_list_neq.
  by rewrite unlock /=; wp_pures.
rewrite {}e.
wp_untag_eq args e; wp_pures.
  rewrite {}e Spec.tagK /=.
  wp_list_of_term_eq args' e; wp_pures; last by rewrite e.
  rewrite {}e Spec.of_listK /=.
  wp_list_match => [???? -> {args'} | neq]; wp_finish; last first.
    by rewrite prod_of_list_neq.
  by rewrite unlock /=; wp_pures.
by rewrite {}e.
Qed.

Lemma wp_check N psk g ke E Φ :
  Φ (repr (term_of <$> check N psk g ke)) -∗
  WP I.check N psk g (term_of ke) @ E {{ Φ }}.
Proof.
iIntros "?"; rewrite /I.check; wp_pures.
iApply wp_case.
case: ke => [psk' cn|g' cn gx|psk' g' cn gx] //=; wp_pures => //.
- wp_tag; wp_hash; wp_eq_term e; wp_pures; try by rewrite decide_False.
  wp_list; wp_term_of_list; wp_tag; wp_pures.
  by rewrite decide_True //=.
- wp_eq_term e; wp_pures; try by rewrite decide_False.
  wp_list; wp_term_of_list; wp_tag; wp_pures.
  by rewrite e decide_True.
- wp_tag; wp_hash; wp_eq_term e; wp_pures; last first.
    rewrite decide_False //; intuition congruence.
  rewrite {}e; wp_eq_term e; wp_pures; last first.
    rewrite decide_False //; intuition congruence.
  wp_list; wp_term_of_list; wp_tag; wp_pures.
  by rewrite decide_True //=.
Qed.

Definition wf ke : iProp :=
  match ke with
  | Psk psk cn =>
    sterm psk ∧ pterm cn
  | Dh g cn x  =>
    pterm g ∧ pterm cn ∧ dh_seed (λ _, True)%I x
  | PskDh psk g cn x =>
    sterm psk ∧
    pterm g ∧ pterm cn ∧ dh_seed (λ _, True)%I x
  end.

#[global]
Instance Persistent_wf ke : Persistent (wf ke).
Proof. case: ke => *; apply _. Qed.

Lemma wf_psk ke : wf ke -∗ sterm (psk ke).
Proof.
case: ke => [psk ?|???|psk ???] /=.
- by iIntros "(? & ?)".
- by iIntros "_"; rewrite sterm_TInt.
- by iIntros "(? & ? & ? & ?)".
Qed.

Lemma wf_encode N ke :
  Keys.ctx N -∗
  wf ke -∗
  pterm (term_of (encode N ke)).
Proof.
iIntros "#(hash & _) #wf".
case: ke => [psk cn|g cn x|psk g cn x] //=.
- iDestruct "wf" as "[??]".
  rewrite pterm_tag pterm_of_list /=; do !iSplit => //.
  rewrite pterm_THash sterm_tag; iRight; iSplit => //.
  by iExists _, _, _; eauto.
- iDestruct "wf" as "(? & ? & ?)".
  rewrite pterm_tag pterm_of_list /=.
  do !iSplit => //.
  iApply dh_pterm_TExp; eauto.
  by iApply pterm_sterm.
- iDestruct "wf" as "(? & ? & ? & ?)".
  rewrite pterm_tag pterm_of_list /=.
  do !iSplit => //.
    rewrite pterm_THash sterm_tag; iRight; iSplit => //.
    by iExists _, _, _; eauto.
  by iApply dh_pterm_TExp; eauto; iApply pterm_sterm.
Qed.

Lemma wp_new ke E Φ :
  Meth.wf ke -∗
  (∀ ke', ⌜ke = meth_of ke'⌝ -∗
          wf ke' -∗
          nonce_meta_token (cnonce ke') ⊤ -∗
          Φ (term_of ke')) -∗
  WP I.new ke @ E {{ Φ }}.
Proof.
iIntros "#p_ke post"; rewrite /I.new; wp_pures.
iApply Meth.wp_case; case: ke => [psk|g|psk g]; wp_pures.
- wp_bind (mknonce _); iApply (wp_mknonce _ (λ _, True)%I (λ _, True)%I).
  iIntros (cn) "_ #p_cn _ token"; wp_list; wp_term_of_list.
  wp_tag.
  iApply ("post" $! (Psk psk cn) with "[] [] token") => //=.
  do !iSplit => //.
  by iApply "p_cn".
- wp_bind (mkdh _); iApply (wp_mkdh (λ _, True)%I g).
  iIntros (a) "_ #p_a _"; wp_list.
  wp_bind (mknonce _); iApply (wp_mknonce _ (λ _, True)%I (λ _, True)%I).
  iIntros (cn) "_ #p_cn _ token"; wp_list; wp_term_of_list.
  wp_tag.
  rewrite (term_meta_token_difference _ ⊤); try set_solver.
  iDestruct "token" as "[token _]".
  iApply ("post" $! (Dh g cn a)) => //=.
  do !iSplit => //.
  by iApply "p_cn".
- wp_bind (mkdh _); iApply (wp_mkdh (λ _, True)%I g).
  iIntros (a) "_ #p_a _"; wp_list.
  wp_bind (mknonce _); iApply (wp_mknonce _ (λ _, True)%I (λ _, True)%I).
  iIntros (cn) "_ #p_cn _ token"; wp_list; wp_term_of_list.
  wp_tag.
  iApply ("post" $! (PskDh psk g cn a)) => //=.
  iDestruct "p_ke" as "(? & ?)".
  do !iSplit => //.
  by iApply "p_cn".
Qed.

Lemma check_Some N psk g ke ke' :
  check N psk g ke = Some ke' →
  ke = encode' N ke' ∧
  Meth.compatible psk g (meth_of ke').
Proof.
case: ke =>> /=.
- by case: decide => [->|//] [<-].
- by case: decide => [->|//] [<-].
- by case: decide => [[-> ->]|//] [<-].
Qed.

End Proofs.

End CShare.

Coercion CShare.term_of : CShare.t >-> term.
#[global]
Existing Instance CShare.Persistent_wf.

(**

Finally, the server share contains the encoded client share together with
fresh keying material chosen by the server.  Note that the serialization
functions do not affect the part that comes from the client.

*)

Module SShare.

Variant t :=
| Psk of term & term & term
| Dh of term & term & term & term & term
| PskDh of term & term & term & term & term & term.

Definition encode N ke :=
  match ke with
  | Psk psk cn sn =>
    Psk (THash (Spec.tag (N.@"psk") psk)) cn sn
  | Dh g cn sn gx y =>
    Dh g cn sn gx (TExp g [y])
  | PskDh psk g cn sn gx y =>
    PskDh (THash (Spec.tag (N.@"psk") psk)) g cn sn gx (TExp g [y])
  end.

Definition encode' N ke :=
  match ke with
  | Psk psk cn sn =>
    Psk (THash (Spec.tag (N.@"psk") psk)) cn sn
  | Dh g cn sn x gy =>
    Dh g cn sn (TExp g [x]) gy
  | PskDh psk g cn sn x gy =>
    PskDh (THash (Spec.tag (N.@"psk") psk)) g cn sn (TExp g [x]) gy
  end.

Definition term_of ke :=
  match ke with
  | Psk psk cn sn =>
    Spec.tag (nroot.@"psk") (Spec.of_list [psk; cn; sn])
  | Dh g cn sn x y =>
    Spec.tag (nroot.@"dh") (Spec.of_list [g; cn; sn; x; y])
  | PskDh psk g cn sn x y =>
    Spec.tag (nroot.@"pskdh") (Spec.of_list [psk; g; cn; sn; x; y])
  end.

Lemma term_of_inj : Inj (=) (=) term_of.
Proof.
move=> ke1 ke2; case: ke1 =>>; case: ke2 =>> /= /Spec.tag_inj [e];
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

Definition session_key_of N ke :=
  Spec.tag (N.@"sess_key") match ke with
  | Psk psk cn sn => Spec.of_list [psk; cn; sn]
  | Dh _ _ _ gx y => Spec.texp gx y
  | PskDh psk _ _ _ gx y => Spec.of_list [psk; Spec.texp gx y]
  end.

(** Similar to the above, but should be called by the client *)

Definition session_key_of' N ke :=
  match ke with
  | Psk psk cn sn =>
    Spec.tag (N.@"sess_key")
             (Spec.of_list [psk; cn; sn])
  | Dh _ _ _ x gy =>
    Spec.tag (N.@"sess_key") (Spec.texp gy x)
  | PskDh psk _ _ _ x gy =>
    Spec.tag (N.@"sess_key") (Spec.of_list [psk; Spec.texp gy x])
  end.

Lemma encode_eq N kex1 kex2 :
  encode' N kex1 = encode N kex2 →
  cnonce kex1 = cnonce kex2 ∧
  snonce kex1 = snonce kex2 ∧
  session_key_of' N kex1 = session_key_of N kex2 ∧
  has_dh kex1 = has_dh kex2 ∧
  psk kex1 = psk kex2 ∧
  meth_of kex1 = meth_of kex2.
Proof.
rewrite /session_key_of.
case: kex1 kex2 => [???|?????|??????] [???|?????|??????] //=.
- by case=> [/Spec.tag_inj [_ ->] -> ->].
- by case=> e_g -> -> <- ->; rewrite e_g !Spec.texpA TExpC2.
- by case=> [] /Spec.tag_inj [_ ->] e_g -> -> <- ->; rewrite e_g !Spec.texpA TExpC2.
Qed.

(** Check a server share against a corresponding client share.  This function
should be used by the client, so the server share is encoded as a term. If the
check succeeds, return the corresponding session key; otherwise, return None. *)

Definition check N c_kex ke :=
  match c_kex with
  | CShare.Psk psk cn =>
    s_kex ← Spec.untag (nroot.@"psk") ke;
    s_kex ← Spec.to_list s_kex;
    '(psk', cn', sn) ← prod_of_list 3 s_kex;
    if decide (psk' = THash (Spec.tag (N.@"psk") psk) ∧ cn' = cn) then
      Some (Psk psk cn sn)
    else None
  | CShare.Dh g cn x =>
    s_kex ← Spec.untag (nroot.@"dh") ke;
    s_kex ← Spec.to_list s_kex;
    '(g', cn', sn, gx, gy) ← prod_of_list 5 s_kex;
    if decide (g' = g ∧ cn' = cn ∧ gx = TExp g [x]) then
      let skey := Spec.tag (N.@"sess_key") (Spec.texp gy x) in
      Some (Dh g cn sn x gy)
    else None
  | CShare.PskDh psk g cn x =>
    s_kex ← Spec.untag (nroot.@"pskdh") ke;
    s_kex ← Spec.to_list s_kex;
    '(psk', g', cn', sn, gx, gy) ← prod_of_list 6 s_kex;
    if decide (psk' = THash (Spec.tag (N.@"psk") psk)
               ∧ g' = g ∧ cn' = cn ∧ gx = TExp g [x]) then
      let skey := Spec.tag (N.@"sess_key") (Spec.texp gy x) in
      Some (PskDh psk g cn sn x gy)
    else None
  end.

Module I.

Definition case : val := λ: "ke" "f_psk" "f_dh" "f_pskdh",
  match: untag (nroot.@"psk") "ke" with
    SOME "args" =>
    bind: "l" := list_of_term "args" in
    list_match: ["psk"; "cn"; "sn"] := "l" in
    "f_psk" "psk" "cn" "sn"
  | NONE =>
  match: untag (nroot.@"dh") "ke" with
    SOME "args" =>
    bind: "l" := list_of_term "args" in
    list_match: ["g"; "cn"; "sn"; "x"; "y"] := "l" in
    "f_dh" "g" "cn" "sn" "x" "y"
  | NONE =>
  match: untag (nroot.@"pskdh") "ke" with
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
      let: "psk" := hash (tag (N.@"psk") "psk") in
      tag (nroot.@"psk") (term_of_list ["psk"; "cn"; "sn"]))
    (λ: "g" "cn" "sn" "gx" "y",
      let: "gy" := texp (tgroup "g") "y" in
      tag (nroot.@"dh") (term_of_list ["g"; "cn"; "sn"; "gx"; "gy"]))
    (λ: "psk" "g" "cn" "sn" "gx" "y",
      let: "psk" := hash (tag (N.@"psk") "psk") in
      let: "gy" := texp (tgroup "g") "y" in
      tag (nroot.@"pskdh") (term_of_list ["psk"; "g"; "cn"; "sn"; "gx"; "gy"])).

Definition session_key_of N : val := λ: "ke",
  case "ke"
    (λ: "psk" "c_nonce" "s_nonce",
       tag (N.@"sess_key") (term_of_list ["psk"; "c_nonce"; "s_nonce"]))
    (λ: <> <> <> "gx" "y", tag (N.@"sess_key") (texp "gx" "y"))
    (λ: "psk" <> <> <> "gx" "y",
       tag (N.@"sess_key") (term_of_list ["psk"; texp "gx" "y"])).

Definition session_key_of' N : val := λ: "ke",
  case "ke"
    (λ: "psk" "c_nonce" "s_nonce",
       tag (N.@"sess_key") (term_of_list ["psk"; "c_nonce"; "s_nonce"]))
    (λ: <> <> <> "x" "gy", tag (N.@"sess_key") (texp "gy" "x"))
    (λ: "psk" <> <> <> "x" "gy",
       tag (N.@"sess_key") (term_of_list ["psk"; texp "gy" "x"])).

Definition check N : val := λ: "c_kex" "s_kex",
  CShare.I.case "c_kex"
    (λ: "psk" "cn",
      bind: "s_kex" := untag (nroot.@"psk") "s_kex" in
      bind: "s_kex" := list_of_term "s_kex" in
      list_match: ["psk'"; "cn'"; "sn"] := "s_kex" in
      if: eq_term "psk'" (hash (tag (N.@"psk") "psk"))
          && eq_term "cn'" "cn" then
        SOME (tag (nroot.@"psk") (term_of_list ["psk"; "cn"; "sn"]))
      else NONE)
    (λ: "g" "cn" "x",
      bind: "s_kex" := untag (nroot.@"dh") "s_kex" in
      bind: "s_kex" := list_of_term "s_kex" in
      list_match: ["g'"; "cn'"; "sn"; "gx"; "gy"] := "s_kex" in
      if: eq_term "g'" "g" && eq_term "cn'" "cn" &&
          eq_term "gx" (texp (tgroup "g") "x") then
        SOME (tag (nroot.@"dh") (term_of_list ["g"; "cn"; "sn"; "x"; "gy"]))
      else NONE)
    (λ: "psk" "g" "cn" "x",
      bind: "s_kex" := untag (nroot.@"pskdh") "s_kex" in
      bind: "s_kex" := list_of_term "s_kex" in
      list_match: ["psk'"; "g'"; "cn'"; "sn"; "gx"; "gy"] := "s_kex" in
      if: eq_term "psk'" (hash (tag (N.@"psk") "psk")) &&
          eq_term "g'" "g" && eq_term "cn'" "cn" &&
          eq_term "gx" (texp (tgroup "g") "x") then
        SOME (tag (nroot.@"pskdh") (term_of_list ["psk"; "g"; "cn"; "sn"; "x"; "gy"]))
      else NONE).

Definition new : val := λ: "ke",
  CShare.I.case "ke"
    (λ: "psk" "c_nonce",
        tag (nroot.@"psk") (term_of_list ["psk"; "c_nonce"; mknonce #()]))
    (λ: "g" "cn" "gx",
      tag (nroot.@"dh") (term_of_list ["g"; "cn"; mknonce #(); "gx"; mkdh #()]))
    (λ: "psk" "g" "cn" "gx",
      tag (nroot.@"pskdh") (term_of_list ["psk"; "g"; "cn"; mknonce #(); "gx"; mkdh #()])).

End I.

Section Proofs.

Context `{!heapGS Σ, cryptisG Σ}.
Notation iProp := (iProp Σ).

Implicit Types t : term.
Implicit Types Φ : val → iProp.

Lemma wp_case ke (f_psk f_dh f_pskdh : val) E Φ :
  match ke with
  | Psk psk c_nonce s_nonce => WP f_psk psk c_nonce s_nonce @ E {{ Φ }}
  | Dh g cn sn x y => WP f_dh g cn sn x y @ E {{ Φ }}
  | PskDh psk g cn sn x y => WP f_pskdh psk g cn sn x y @ E {{ Φ }}
  end -∗
  WP I.case (term_of ke) f_psk f_dh f_pskdh @ E {{ Φ }}.
Proof.
iIntros "post"; rewrite /I.case.
wp_untag_eq psk e_psk.
  case: ke e_psk => [???|?????|??????] /= /Spec.tag_inj []; try set_solver.
  move=> _ <-; wp_pures; do !rewrite subst_list_match /=.
  wp_list_of_term_eq l e_l; last by rewrite Spec.of_listK in e_l.
  move/Spec.of_list_inj: e_l => {l} <-.
  by wp_list_match => // _ _ _ [<- <- <-].
wp_untag_eq args e_dh.
  case: ke e_psk e_dh => [???|g cn sn x y|??????] /= e_psk /Spec.tag_inj [];
    try set_solver.
  move=> _ <- {e_psk args}; wp_pures; do !rewrite subst_list_match /=.
  wp_list_of_term_eq l e_l; last by rewrite Spec.of_listK in e_l.
  move/Spec.of_list_inj: e_l => {l} <-.
  by wp_list_match => // _ _ _ _ _ [<- <- <- <- <-].
wp_untag_eq args e_pskdh; last first.
  by case: ke e_psk e_dh e_pskdh =>> /=; rewrite Spec.tagK.
case: ke e_psk e_dh e_pskdh
  => [???|?????|psk g cn sn x y] /= e_psk e_dh /Spec.tag_inj []; try set_solver.
move=> _ <- {e_psk e_dh args}; wp_pures; do !rewrite subst_list_match /=.
wp_list_of_term_eq l e_l; last by rewrite Spec.of_listK in e_l.
move/Spec.of_list_inj: e_l => {l} <-.
by wp_list_match => // _ _ _ _ _ _ [<- <- <- <- <- <-].
Qed.

Lemma wp_cnonce ke E Φ :
  Φ (cnonce ke) -∗
  WP I.cnonce (term_of ke) @ E {{ Φ }}.
Proof.
rewrite /I.cnonce; iIntros "post"; wp_pures.
by iApply wp_case; case: ke =>>; wp_pures.
Qed.

Lemma wp_snonce ke E Φ :
  Φ (snonce ke) -∗
  WP I.snonce (term_of ke) @ E {{ Φ }}.
Proof.
rewrite /I.snonce; iIntros "post"; wp_pures.
by iApply wp_case; case: ke =>>; wp_pures.
Qed.

Lemma wp_encode N ke E Φ :
  Φ (term_of (encode N ke)) -∗
  WP I.encode N (term_of ke) @ E {{ Φ }}.
Proof.
iIntros "post"; rewrite /I.encode; wp_pures.
iApply wp_case.
case: ke => [psk c_nonce s_nonce|g cn sn gx y|psk g cn sn gx y] /=; wp_pures.
- wp_tag; wp_hash.
  by wp_list; wp_term_of_list; wp_tag.
- wp_bind (tgroup _); iApply wp_tgroup.
  wp_bind (texp _ _); iApply wp_texp; wp_pures.
  rewrite Spec.texpA.
  wp_list; wp_term_of_list.
  by iApply wp_tag.
- wp_tag; wp_hash; wp_pures.
  wp_bind (tgroup _); iApply wp_tgroup.
  wp_bind (texp _ _); iApply wp_texp; wp_pures.
  rewrite Spec.texpA.
  wp_list; wp_term_of_list.
  by iApply wp_tag.
Qed.

Lemma wp_session_key_of N ke E Φ :
  Φ (session_key_of N ke) -∗
  WP I.session_key_of N (term_of ke) @ E {{ Φ }}.
Proof.
iIntros "?"; rewrite /I.session_key_of; wp_pures.
iApply wp_case.
case: ke => [???|?????|??????]; wp_pures.
- by wp_list; wp_term_of_list; wp_tag.
- by wp_bind (texp _ _); iApply wp_texp; wp_tag.
- by wp_list; wp_bind (texp _ _); iApply wp_texp; wp_list; wp_term_of_list; wp_tag.
Qed.

Lemma wp_session_key_of' N ke E Φ :
  Φ (session_key_of' N ke) -∗
  WP I.session_key_of' N (term_of ke) @ E {{ Φ }}.
Proof.
iIntros "?"; rewrite /I.session_key_of'; wp_pures.
iApply wp_case.
case: ke => [???|?????|??????]; wp_pures.
- by wp_list; wp_term_of_list; wp_tag.
- by wp_bind (texp _ _); iApply wp_texp; wp_tag.
- by wp_list; wp_bind (texp _ _); iApply wp_texp; wp_list; wp_term_of_list; wp_tag.
Qed.

Lemma wp_check N c_kex s_kex E Φ :
  Φ (repr (term_of <$> check N c_kex s_kex)) -∗
  WP I.check N (CShare.term_of c_kex) s_kex @ E {{ Φ }}.
Proof.
iIntros "?"; rewrite /I.check; wp_pures.
iApply CShare.wp_case.
case: c_kex => [psk c_nonce|g cn x|psk g cn x] /=; wp_pures.
- wp_untag_eq s_kex' e; last by wp_pures; rewrite e.
  rewrite {}e Spec.tagK /=.
  wp_list_of_term_eq l e; last by wp_pures; rewrite e.
  rewrite {}e Spec.of_listK /=.
  wp_list_match => [psk' c_nonce' s_nonce ->|ne] //=; wp_finish; last first.
    by rewrite prod_of_list_neq //=.
  rewrite unlock /=.
  wp_tag; wp_hash; wp_eq_term e; last first.
    rewrite decide_False; try by intuition congruence.
    by wp_pures.
  rewrite {}e; wp_eq_term e; last first.
    rewrite decide_False; try by intuition congruence.
    by wp_pures.
  rewrite e decide_True //; wp_pures.
  wp_list; wp_term_of_list; wp_pures.
  wp_tag.
  by wp_list; wp_pures.
- wp_untag_eq s_kex' e; last by wp_pures; rewrite e.
  rewrite {}e Spec.tagK /=.
  wp_list_of_term_eq l e; last by wp_pures; rewrite e.
  rewrite {}e Spec.of_listK /=.
  wp_list_match => [g' cn' sn gx gy ->|ne] //=; wp_finish; last first.
    by rewrite prod_of_list_neq //=.
  rewrite [in prod_of_list _ _]unlock /=.
  wp_eq_term e; last first.
    rewrite decide_False; try by intuition congruence.
    by wp_pures.
  rewrite {}e; wp_eq_term e; last first.
    rewrite decide_False; try by intuition congruence.
    by wp_pures.
  rewrite {}e; wp_pures; wp_bind (tgroup _); iApply wp_tgroup.
  wp_bind (texp _ _); iApply wp_texp; rewrite Spec.texpA.
  wp_eq_term e; last first.
    rewrite decide_False; try by intuition congruence.
    by wp_pures.
  rewrite e decide_True //; wp_pures.
  wp_list; wp_term_of_list.
  wp_tag; wp_pures.
  by iModIntro.
- wp_untag_eq s_kex' e; last by wp_pures; rewrite e.
  rewrite {}e Spec.tagK /=.
  wp_list_of_term_eq l e; last by wp_pures; rewrite e.
  rewrite {}e Spec.of_listK /=.
  wp_list_match => [psk' g' cn' sn gx gy ->|ne] //=; wp_finish; last first.
    by rewrite prod_of_list_neq //=.
  rewrite [in prod_of_list _ _]unlock /=.
  wp_tag; wp_hash; wp_eq_term e; last first.
    rewrite decide_False; try by intuition congruence.
    by wp_pures.
  rewrite {}e; wp_eq_term e; last first.
    rewrite decide_False; try by intuition congruence.
    by wp_pures.
  rewrite {}e; wp_eq_term e; last first.
    rewrite decide_False; try by intuition congruence.
    by wp_pures.
  rewrite {}e; wp_pures; wp_bind (tgroup _); iApply wp_tgroup.
  wp_bind (texp _ _); iApply wp_texp; rewrite Spec.texpA.
  wp_eq_term e; last first.
    rewrite decide_False; try by intuition congruence.
    by wp_pures.
  rewrite e decide_True //; wp_pures.
  wp_list; wp_term_of_list.
  wp_tag; wp_pures.
  by iModIntro.
Qed.

Definition wf ke : iProp :=
  match ke with
  | Psk psk c_nonce s_nonce =>
    sterm psk ∧ pterm c_nonce ∧ pterm s_nonce
  | Dh g cn sn gx y =>
    pterm g ∧ pterm cn ∧ pterm sn ∧ pterm gx ∧
    dh_seed (λ _, True)%I y
  | PskDh psk g cn sn gx y =>
    sterm psk ∧
    pterm g ∧ pterm cn ∧ pterm sn ∧
    pterm gx ∧
    dh_seed (λ _, True)%I y
  end.

#[global]
Instance Persistent_wf ke : Persistent (wf ke).
Proof. case: ke => *; apply _. Qed.

Lemma wp_new N psk g (ke : CShare.t) E Φ :
  Meth.compatible psk g (CShare.meth_of ke) →
  sterm psk -∗
  pterm g -∗
  pterm (CShare.encode' N ke) -∗
  (∀ ke',
      ⌜ke = cshare_of ke'⌝ -∗
      wf ke' -∗
      nonce_meta_token (snonce ke') ⊤ -∗
      Φ (term_of ke')) -∗
  WP I.new ke @ E {{ Φ }}.
Proof.
iIntros (e_check) "#s_psk #p_g #p_ke post"; rewrite /I.new; wp_pures.
iApply CShare.wp_case.
case: ke => [psk' cn|g' cn gx|psk' g' cn gx] /= in e_check *; wp_pures.
- subst psk.
  wp_bind (mknonce _); iApply (wp_mknonce _ (λ _, True)%I (λ _, True)%I).
  iIntros (a) "_ #pred_a _ token"; wp_list; wp_term_of_list.
  wp_tag; iModIntro.
  iApply ("post" $! (Psk _ _ a)) => //=.
  rewrite pterm_tag pterm_of_list /=.
  iDestruct "p_ke" as "(_ & p_cn & _)".
  do !iSplit => //.
  by iApply "pred_a".
- subst g'.
  wp_bind (mkdh _); iApply (wp_mkdh (λ _, True)%I g).
  iIntros (a) "_ #pred_a _"; wp_list.
  wp_bind (mknonce _); iApply (wp_mknonce _ (λ _, True)%I (λ _, True)%I).
  iIntros (sn) "_ #p_sn _ token"; wp_list; wp_term_of_list.
  wp_tag; iModIntro.
  iApply ("post" $! (Dh g cn sn gx a)) => //=.
  rewrite !pterm_tag !pterm_of_list /=.
  iDestruct "p_ke" as "(? & ? & ? & _)".
  do !iSplit => //.
  by iApply "p_sn".
- case: e_check=> -> ->.
  wp_bind (mkdh _); iApply (wp_mkdh (λ _, True)%I g).
  iIntros (a) "_ #pred_a _"; wp_list.
  wp_bind (mknonce _); iApply (wp_mknonce _ (λ _, True)%I (λ _, True)%I).
  iIntros (sn) "_ #p_sn _ token"; wp_list; wp_term_of_list.
  wp_tag; iModIntro.
  iApply ("post" $! (PskDh _ g cn sn gx a)) => //.
  rewrite !pterm_tag !pterm_of_list /=.
  iDestruct "p_ke" as "(? & ? & ? & ? & _)".
  do !iSplit => //.
  by iApply "p_sn".
Qed.

Lemma pterm_checkE N c_kex ke ke' :
  check N c_kex ke = Some ke' →
  c_kex = cshare_of ke' ∧ ke = term_of (encode' N ke').
Proof.
case: c_kex => [psk cn|g cn x|psk g cn x] /=.
- case: Spec.untagP => //= {}ke ->.
  case: Spec.to_listP=> //= {}ke.
  elim/(@list_len_rect 3): ke => [psk' cn' sn|ke neq]; last first.
    by rewrite prod_of_list_neq.
  rewrite unlock /=; case: decide => //= - [] {psk' cn'} -> -> [] {ke'} <-.
  by split => //.
- case: Spec.untagP => //= {}ke ->.
  case: Spec.to_listP => //= {}ke.
  elim/(@list_len_rect 5): ke => [g' cn' sn gx gy|ke neq]; last first.
    by rewrite prod_of_list_neq.
  rewrite [prod_of_list _ _]unlock /=; case: decide => //= - [] -> [] -> ->.
  case=> [] {ke'} <-.
  by split => //.
- case: Spec.untagP => //= {}ke ->.
  case: Spec.to_listP => //= {}ke.
  elim/(@list_len_rect 6): ke => [psk' g' cn' sn gx gy|ke neq]; last first.
    by rewrite prod_of_list_neq.
  rewrite [prod_of_list _ _]unlock /=.
  case: decide => //= - [] -> [] -> [] -> -> [] {ke'} <-.
  by split.
Qed.

Lemma pterm_cnonce ke : pterm (term_of ke) -∗ pterm (cnonce ke).
Proof.
case: ke=> * /=; rewrite pterm_tag pterm_of_list /=.
- by iIntros "(? & ? & ?)".
- by iIntros "(? & ? & ?)".
- by iIntros "(? & ? & ? & ?)".
Qed.

Lemma pterm_snonce ke : pterm (term_of ke) -∗ pterm (snonce ke).
Proof.
case: ke=> * /=; rewrite pterm_tag pterm_of_list /=.
- by iIntros "(? & ? & ? & ?)".
- by iIntros "(? & ? & ? & ?)".
- by iIntros "(? & ? & ? & ? & ?)".
Qed.

Lemma pterm_encode N ke :
  Keys.ctx N -∗
  wf ke -∗
  pterm (term_of (encode N ke)).
Proof.
iIntros "#(? & _)".
case: ke=>> /=.
- iIntros "#(s_psk & p_cn & p_sn)".
  rewrite pterm_tag pterm_of_list /=.
  do !iSplit => //.
  rewrite pterm_THash; iRight.
  rewrite sterm_tag; iSplit => //.
  by iExists _, _, _; eauto.
- iIntros "#(p_g & p_cn & p_sn & p_gx & seed_y)".
  rewrite pterm_tag pterm_of_list /=.
  do !iSplit => //.
  iApply dh_pterm_TExp; eauto.
  by iApply pterm_sterm.
- iIntros "#(p_psk & p_g & p_cn & p_sn & p_gx & seed_y)".
  rewrite pterm_tag pterm_of_list /=.
  do !iSplit => //.
  + rewrite pterm_THash; iRight.
    rewrite sterm_tag; iSplit => //.
    by iExists _, _, _; eauto.
  + iApply dh_pterm_TExp; eauto.
    by iApply pterm_sterm.
Qed.

Lemma sterm_session_key_of N ke : wf ke -∗ sterm (session_key_of N ke).
Proof.
case: ke=>> /=.
- iIntros "#(?&?&?)".
  by rewrite sterm_tag sterm_of_list /=; do !iSplit => //; iApply pterm_sterm.
- iIntros "#(?&?&?&?&seed)".
  rewrite sterm_tag; iApply sterm_texp => //.
  + by iApply pterm_sterm.
  + by iDestruct "seed" as "(?&?)".
- iIntros "#(?&?&?&?&?&seed)".
  rewrite sterm_tag sterm_of_list /=; do !iSplit => //.
  iApply sterm_texp => //.
  + by iApply pterm_sterm.
  + by iDestruct "seed" as "(?&?)".
Qed.

Lemma pterm_session_key_of' N kt ke :
  Keys.ctx N -∗
  pterm (TKey kt (SShare.session_key_of' N ke)) -∗
  ◇ pterm (SShare.psk ke).
Proof.
case: ke => [psk| |psk] > /=;
rewrite pterm_TKey pterm_tag ?pterm_of_list /=.
- iIntros "#(_ & ?) #[p_k | (_ & p_k)]".
  + by iDestruct "p_k" as "(? & _)".
  + iDestruct (wf_key_elim with "p_k []") as "#H"; eauto.
    by iDestruct "H" as ">[]".
- by iIntros "_ _"; rewrite pterm_TInt.
- iIntros "#(_ & ?) #[p_k | (_ & p_k)]".
  + by iDestruct "p_k" as "(? & _)".
  + iDestruct (wf_key_elim with "p_k []") as "#H"; eauto.
    by iDestruct "H" as ">[]".
Qed.

Lemma pterm_session_key_ofW N kex kt :
  Keys.ctx N -∗
  wf kex -∗
  pterm (TKey kt (session_key_of N kex)) -∗
  ◇ pterm (psk kex).
Proof.
iIntros "# (? & ?)".
case: kex => [psk cn sn|g cn sn gx y|psk g cn sn gx y] /=.
- iIntros "#(s_psk & p_cn & p_sn)".
  + rewrite pterm_TKey; iDestruct 1 as "#[p_k|[_ p_k]]".
    * by rewrite pterm_tag pterm_of_list /=; iDestruct "p_k" as "(? & ? & ?)".
    * iPoseProof (wf_key_elim with "p_k []") as "{p_k} #p_k"; eauto.
      by iMod "p_k" as "?".
- by rewrite pterm_TInt /=; eauto.
- iIntros "#(_ & _ & _ & _ & p_gx & dh_y)".
  rewrite /session_key_of /=.
  rewrite pterm_TKey pterm_tag; iDestruct 1 as "#[p_k|[_ p_k]]".
  + by rewrite pterm_of_list /=; iDestruct "p_k" as "(p_psk & _ & _)".
  + iDestruct (wf_key_elim with "p_k []") as "{p_k} #p_exp"; eauto.
    by iMod "p_exp" as "?".
Qed.

Lemma pterm_session_key_of N c_kex s_kex kt :
  encode' N c_kex = encode N s_kex →
  Keys.ctx N -∗
  CShare.wf (cshare_of c_kex) -∗
  wf s_kex -∗
  pterm (TKey kt (session_key_of N s_kex)) -∗
  ◇ if has_dh c_kex then False else pterm (psk c_kex).
Proof.
iIntros (e) "# (? & ?)".
case: c_kex e => [psk cn sn|g cn sn x gy|psk g cn sn x gy] /=.
- case: s_kex => //= _ _ _ [] /Spec.tag_inj [_ <-] <- <-.
  iIntros "_ #(s_psk & p_cn & p_sn)".
  + rewrite pterm_TKey; iDestruct 1 as "#[p_k|[_ p_k]]".
    * by rewrite pterm_tag pterm_of_list /=; iDestruct "p_k" as "(? & ? & ?)".
    * iPoseProof (wf_key_elim with "p_k []") as "{p_k} #p_k"; eauto.
      by iMod "p_k" as "?".
- case: s_kex => //= _ ? ? gx y [] <- _ _ <- e2.
  rewrite /session_key_of Spec.texpA.
  iIntros "#(p_g & _ & dh_x)".
  iIntros "#(_ & _ & _ & p_gx & dh_y)".
  rewrite pterm_TKey pterm_tag; iDestruct 1 as "#[p_k|[_ p_k]]".
  + iMod (dh_seed_elim2 with "dh_y p_k") as "[_ p_x]".
    iMod (dh_seed_elim0 with "dh_x p_x") as "[]".
  + iDestruct (wf_key_elim with "p_k []") as "{p_k} #p_exp"; eauto.
    by iMod "p_exp" as "?".
- case: s_kex => //= _ ? ? ? gx y [] /Spec.tag_inj [_ <-].
  move=> <- _ _ <- e2.
  iIntros "#(_ & _ & _ & dh_x)".
  iIntros "#(_ & _ & _ & _ & p_gx & dh_y)".
  rewrite /session_key_of.
  rewrite Spec.texpA pterm_TKey pterm_tag; iDestruct 1 as "#[p_k|[_ p_k]]".
  + rewrite pterm_of_list /=; iDestruct "p_k" as "(_ & p_k & _)".
    iMod (dh_seed_elim2 with "dh_y p_k") as "[_ p_x]".
    by iMod (dh_seed_elim0 with "dh_x p_x") as "[]".
  + iDestruct (wf_key_elim with "p_k []") as "{p_k} #p_exp"; eauto.
    by iMod "p_exp" as "?".
Qed.

End Proofs.

End SShare.

Coercion SShare.term_of : SShare.t >-> term.
#[global]
Existing Instance SShare.Persistent_wf.

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
  THash (Spec.tag (N.@"binder") (Spec.of_list [psk; ch])).

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
  let mac' := THash (Spec.tag (N.@"binder") (Spec.of_list [psk; ch])) in
  if decide (other' = other ∧ mac' = mac) then Some ke else None.

Module I.

Definition hello N : val := λ: "cp",
  bind: "cp" := list_of_term "cp" in
  list_match: ["kex"; "other"] := "cp" in
  let: "ts" := term_of_list [CShare.I.encode N "kex"; "other"] in
  let: "psk" := CShare.I.psk "kex" in
  let: "mac" := hash (tag (N.@"binder") (term_of_list ["psk"; "ts"])) in
  term_of_list ["ts"; "mac"].

Definition check N : val := λ: "psk" "g" "other" "ch",
  bind: "ch" := list_of_term "ch" in
  list_match: ["ch"; "mac"] := "ch" in
  bind: "ch'" := list_of_term "ch" in
  list_match: ["ke"; "other'"] := "ch'" in
  bind: "ke" := CShare.I.of_term "ke" in
  bind: "ke" := CShare.I.check N "psk" "g" "ke" in
  let: "psk" := CShare.I.psk "ke" in
  let: "mac'" := hash (tag (N.@"binder") (term_of_list ["psk"; "ch"])) in
  if: eq_term "other'" "other" && eq_term "mac'" "mac" then SOME "ke" else NONE.

End I.

Section Proofs.

Context `{!heapGS Σ, cryptisG Σ}.
Notation iProp := (iProp Σ).

Implicit Types t : term.
Implicit Types Φ : val → iProp.

Lemma wp_hello N cp E Φ :
  Φ (hello N cp) -∗
  WP I.hello N (term_of cp) @ E {{ Φ }}.
Proof.
iIntros "post"; rewrite /I.hello; wp_pures.
wp_list_of_term_eq t e; last by rewrite Spec.of_listK in e.
move/Spec.of_list_inj: e => <-.
wp_list_match => // _ _ [] <- <-.
wp_list; wp_bind (CShare.I.encode _ _); iApply CShare.wp_encode.
wp_list; wp_term_of_list; wp_pures.
wp_bind (CShare.I.psk _); iApply CShare.wp_psk.
wp_pures; wp_list; wp_term_of_list; wp_tag; wp_hash.
by wp_pures; wp_list; iApply wp_term_of_list.
Qed.

Lemma wp_check N psk g other ch E Φ :
  Φ (repr (CShare.term_of <$> check N psk g other ch)) -∗
  WP I.check N psk g other ch @ E {{ Φ }}.
Proof.
iIntros "?"; rewrite /check /I.check.
wp_pures.
wp_list_of_term_eq l e; wp_pures; last by rewrite e.
rewrite {}e Spec.of_listK /=.
wp_list_match => [ch' mac -> {l}|ne]; wp_finish; last first.
  by rewrite prod_of_list_neq.
rewrite [in prod_of_list _ [ch'; mac]]unlock /=.
wp_list_of_term_eq l e; wp_pures; last by rewrite e.
rewrite {}e Spec.of_listK /=.
wp_list_match => [ke other' -> {l}|neq]; wp_finish; last first.
  by rewrite prod_of_list_neq.
rewrite [in prod_of_list _ [ke; other']]unlock /=.
wp_bind (CShare.I.of_term _); iApply CShare.wp_of_term.
case e: CShare.of_term => [ke'|] //=; wp_pures => //.
wp_bind (CShare.I.check _ _ _ _); iApply CShare.wp_check.
case: CShare.check => [c_ke|] /=; wp_pures => //.
wp_bind (CShare.I.psk _); iApply CShare.wp_psk; wp_pures.
wp_list; wp_term_of_list; wp_tag; wp_hash.
wp_eq_term e'; wp_pures; last first.
  rewrite decide_False //; intuition congruence.
rewrite {}e' {other'}.
wp_eq_term e'; wp_pures; last first.
  rewrite decide_False //; intuition congruence.
by rewrite {}e' decide_True //.
Qed.

Definition wf N cp : iProp :=
  CShare.wf (share cp) ∧
  nonce_meta (CShare.cnonce (share cp)) (N.@"binder") (other cp) ∧
  pterm (other cp).

#[global]
Instance wf_persistent N cp : Persistent (wf N cp).
Proof. apply _. Qed.

Lemma wf_set N cp :
  CShare.wf (share cp) -∗
  nonce_meta_token (CShare.cnonce (share cp)) (↑N.@"binder") -∗
  pterm (other cp) ==∗
  wf N cp.
Proof.
iIntros "#? token #?".
iMod (term_meta_set _ _ (other cp) with "token") as "meta"; eauto.
by iModIntro; do !iSplit.
Qed.

Definition binder_inv N m : iProp :=
  ∃ cp, ⌜m = Spec.of_list [CShare.psk (share cp);
                           hello_pub N cp]⌝ ∧
        ⌜CShare.has_psk (share cp)⌝ ∧
        wf N cp.

Definition ctx N : iProp :=
  Keys.ctx N ∧
  hash_pred (N.@"binder") (binder_inv N).

#[global]
Instance ctx_persistent N : Persistent (ctx N).
Proof. apply _. Qed.

Lemma ctx_alloc N E E' :
  ↑N.@"binder" ⊆ E →
  Keys.ctx N -∗
  hash_pred_token E ={E'}=∗
  ctx N ∗
  hash_pred_token (E ∖ ↑N.@"binder").
Proof.
iIntros (?) "#? token".
iMod (hash_pred_set (N.@"binder") (binder_inv N) with "token") as "[??]"; eauto.
iFrame. by iModIntro.
Qed.

Lemma pterm_hello N cp : ctx N -∗ wf N cp -∗ pterm (hello N cp).
Proof.
iIntros "#[ctx binder] # (wf_cp & meta & p_cp)".
iAssert (pterm (hello_pub N cp)) as "p_pub".
  rewrite pterm_of_list /=; do !iSplit => //.
  by iApply CShare.wf_encode.
rewrite [pterm (hello _ _)]pterm_of_list /=; do ![iSplit => //].
case e: (CShare.has_psk (share cp)); last first.
  rewrite pterm_THash; iLeft; rewrite pterm_tag pterm_of_list /=.
  do ![iSplit => //].
  case: (share cp) e => //= > _; by rewrite pterm_TInt.
rewrite pterm_THash; iRight; rewrite sterm_tag sterm_of_list /=.
do !iSplit => //.
- by iApply CShare.wf_psk.
- by iApply pterm_sterm.
iExists _, _, _; do !iSplit => //; eauto.
iExists cp; iModIntro; do !iSplit => //.
by rewrite e.
Qed.

Lemma pterm_checkE N psk g other ch ke :
  check N psk g other ch = Some ke →
  ctx N -∗
  pterm ch -∗
  ⌜Meth.compatible psk g (CShare.meth_of ke)⌝ ∧
  pterm (CShare.encode' N ke) ∧
  ▷ (pterm (CShare.psk ke) ∨
     ⌜CShare.has_psk ke⌝ ∧
     ∃ ke', ⌜CShare.encode' N ke = CShare.encode N ke'⌝ ∧
            CShare.wf ke' ∧
            nonce_meta (CShare.cnonce ke') (N.@"binder") other).
Proof.
rewrite /check.
case: Spec.to_listP=> //= {}ch.
elim/(list_len_rect 2): ch => [ch mac|ch neq]; last first.
  by rewrite prod_of_list_neq.
rewrite unlock /=.
case: Spec.to_listP=> //= {}ch.
elim/(list_len_rect 2): ch => [ke' other'|ch neq]; last first.
  by rewrite prod_of_list_neq.
rewrite unlock /=.
case e_of_term: CShare.of_term => [ke''|] //=.
move: ke'' e_of_term => {}ke' /CShare.of_termK ->.
case e_check: CShare.check => [c_ke|] //= e.
move: c_ke e_check => {}ke' /CShare.check_Some [-> comp] in e *.
case: decide e => [[-> <-]|//] /= [<-].
iIntros "#(_ & binder_ctx) #p_ch"; iSplit => //.
do ![rewrite pterm_of_list /=]; rewrite pterm_THash pterm_tag.
iDestruct "p_ch" as  "((p_ke' & _) & p_ch & _)"; iSplit => //.
iDestruct "p_ch" as "[fail|succ]".
  do ![rewrite pterm_of_list /=].
  by iDestruct "fail" as "(fail & _ & _)"; eauto.
iDestruct "succ" as "[s_binder wf]".
iDestruct (wf_hash_elim with "wf binder_ctx") as "{wf} #wf".
iModIntro; iRight.
iDestruct "wf" as (cp) "(%e & psk & wf)".
case/Spec.of_list_inj: e => e_psk /Spec.of_list_inj [e_encode ->].
move/CShare.term_of_inj in e_encode.
iSplit; first by case: (ke') e_encode =>>; case: (share cp).
iExists (share cp); iSplit=> //.
by iDestruct "wf" as "(? & ? & ?)"; eauto.
Qed.

End Proofs.

End CParams.

Coercion CParams.term_of : CParams.t >-> term.
#[global]
Existing Instance CParams.wf_persistent.
#[global]
Existing Instance CParams.ctx_persistent.

Module SParams.

Record t := Params {
  share : SShare.t;
  verif_key : term;
  other : term;
}.

Definition encode N sp :=
  {| share := SShare.encode N (share sp);
     verif_key := verif_key sp;
     other := other sp |}.

Definition term_of sp :=
  Spec.of_list [
    SShare.term_of (share sp);
    verif_key sp;
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
    TKey Dec (verif_key sp);
    TEnc (verif_key sp) (Spec.tag (N.@"server_hello_sig") (THash pub))
  ].

Definition hello N sp :=
  let pub := hello_pub N sp in
  let enc := hello_priv N sp in
  let session_key := SShare.session_key_of N (share sp) in
  Spec.of_list [
    pub;
    TEnc session_key (Spec.tag (N.@"server_hello") enc)
  ].

Definition verify N k x sig :=
  match Spec.tdec N k sig with
  | Some y => bool_decide (y = THash x)
  | None => false
  end.

Definition check N cp sp :=
  sp ← Spec.to_list sp;
  '(pub, sig) ← prod_of_list 2 sp;
  pub' ← Spec.to_list pub;
  '(kex, other') ← prod_of_list 2 pub';
  res ← SShare.check N (CParams.share cp) kex;
  let session_key := SShare.session_key_of' N res in
  dec_sig ← Spec.tdec (N.@"server_hello") (TKey Dec session_key) sig;
  dec_sig ← Spec.to_list dec_sig;
  '(verif_key, sig) ← prod_of_list 2 dec_sig;
  if decide (other' = CParams.other cp) then
    if verify (N.@"server_hello_sig") verif_key pub sig then
      Some (verif_key, res)
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
    let: "verif_key" := mkkey "verif_key" in
    let: "enc" :=
      tenc (N.@"server_hello_sig") (Fst "verif_key") (hash "pub") in
    let: "enc" := term_of_list [Snd "verif_key"; "enc"] in
    let: "session_key" := mkkey (SShare.I.session_key_of N "kex") in
    let: "enc" := tenc (N.@"server_hello") (Fst "session_key") "enc" in
    term_of_list ["pub"; "enc"]
  ).

Definition verify N : val := λ: "k" "x" "sig",
  match: tdec N "k" "sig" with
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
  let: "session_key" := SShare.I.session_key_of' N "res" in
  let: "sk" := mkkey "session_key" in
  bind: "dec_sig" := tdec (N.@"server_hello") (Snd "sk") "sig" in
  bind: "dec_sig" := list_of_term "dec_sig" in
  list_match: ["verif_key"; "sig"] := "dec_sig" in
  if: eq_term "s_other" "c_other" then
    if: verify (N.@"server_hello_sig") "verif_key" "pub" "sig" then
      SOME ("verif_key", "res")
    else NONE
  else NONE.

End I.

Section Proofs.

Context `{!heapGS Σ, cryptisG Σ}.
Notation iProp := (iProp Σ).

Implicit Types t : term.
Implicit Types Φ : val → iProp.

Lemma wp_case sp (f : val) E Φ :
  WP f (share sp)
       (verif_key sp)
       (other sp) @ E {{ Φ }} -∗
  WP I.case (term_of sp) f @ E {{ Φ }}.
Proof.
iIntros "?"; rewrite /I.case; wp_pures.
wp_list_of_term_eq l e; last by rewrite Spec.of_listK in e.
move/Spec.of_list_inj: e => {l} <-.
by wp_list_match => // _ _ _ [] <- <- <-.
Qed.

Lemma wp_hello_pub N sp E Φ :
  Φ (hello_pub N sp) -∗
  WP I.hello_pub N (term_of sp) @ E {{ Φ }}.
Proof.
iIntros "?"; rewrite /I.hello_pub; wp_pures.
iApply wp_case; wp_pures.
wp_list.
wp_bind (SShare.I.encode _ _); iApply SShare.wp_encode.
by wp_list; wp_term_of_list.
Qed.

Lemma wp_hello N sp E Φ :
  Φ (hello N sp) -∗
  WP I.hello N (term_of sp) @ E {{ Φ }}.
Proof.
iIntros "?"; rewrite /I.hello; wp_pures.
iApply wp_case; wp_pures.
wp_bind (I.hello_pub _ _); iApply wp_hello_pub; wp_pures.
wp_bind (mkkey _); iApply wp_mkkey; wp_pures.
wp_hash; wp_tenc; wp_pures.
wp_list; wp_term_of_list; wp_pures.
wp_bind (SShare.I.session_key_of _ _); iApply SShare.wp_session_key_of.
wp_bind (mkkey _); iApply wp_mkkey; wp_pures.
by wp_tenc; wp_pures; wp_list; wp_term_of_list.
Qed.

Lemma wp_verify N k x sig E Φ :
  Φ #(verify N k x sig) -∗
  WP I.verify N k x sig @ E {{ Φ }}.
Proof.
iIntros "?"; rewrite /I.verify; wp_pures.
wp_bind (tdec _ _ _); iApply wp_tdec.
rewrite /verify; case e: Spec.tdec => [y|]; wp_pures => //.
by wp_hash; iApply wp_eq_term.
Qed.

Lemma wp_check N cp sh E Φ :
  Φ (repr ((λ '(t, kex), (t, SShare.term_of kex)) <$> check N cp sh)) -∗
  WP I.check N cp sh @ E {{ Φ }}.
Proof.
iIntros "?"; rewrite /I.check /check; wp_pures.
wp_list_of_term_eq l e; last by rewrite Spec.of_listK in e.
move/Spec.of_list_inj: e => <- {l}; wp_pures.
wp_list_match => // _ _ [] <- <-; wp_finish.
wp_list_of_term_eq l e; last by rewrite e; wp_pures.
rewrite {}e Spec.of_listK /=; wp_pures.
wp_list_match => [pub sig -> {l}|ne]; last first.
  by rewrite prod_of_list_neq //=; wp_finish.
rewrite [in prod_of_list 2 [pub; sig]]unlock /=.
wp_list_of_term_eq pub' e; last by rewrite e; wp_pures.
rewrite {}e Spec.of_listK {pub} /=.
wp_list_match => [s_kex s_other -> {pub'}|ne]; last first.
  by rewrite prod_of_list_neq //=; wp_finish.
rewrite [in prod_of_list 2 [s_kex; s_other]]unlock /=.
wp_bind (SShare.I.check _ _ _); iApply SShare.wp_check.
case: SShare.check => [res|]; wp_pures => //=.
wp_bind (SShare.I.session_key_of' _ _); iApply SShare.wp_session_key_of'.
wp_pures.
wp_bind (mkkey _); iApply wp_mkkey; wp_pures.
wp_tdec_eq dec_sig e; last by rewrite e; wp_pures.
rewrite {}e /= /Spec.tdec /= decide_True // Spec.tagK /=.
wp_list_of_term_eq l e; wp_pures; last by rewrite e.
rewrite {}e Spec.of_listK {dec_sig} /=.
wp_list_match=> [verif_key sig' -> {l}|ne]; wp_finish; last first.
  by rewrite prod_of_list_neq //=.
rewrite [in prod_of_list 2 [verif_key; sig']]unlock /=.
wp_eq_term e; wp_pures; last by rewrite decide_False.
rewrite {}e decide_True //= {s_other}.
wp_bind (I.verify _ _ _ _); iApply wp_verify.
by case: verify; wp_pures.
Qed.

Context `{!sessionG Σ}.
Variable (N : namespace) (P : role → term → term → Meth.t * term * term → iProp).

Definition hello_pred (k t : term) : iProp := ∃ sp,
  let ss := share sp in
  ⌜t = hello_priv N sp⌝ ∧
  SShare.wf ss ∧
  session (N.@"sess") Resp (SShare.cnonce ss) (SShare.snonce ss)
          (SShare.meth_of ss, SShare.session_key_of N ss, other sp).

Definition hello_sig_pred (k t : term) : iProp := ∃ kex other,
  ⌜t = THash (Spec.of_list [SShare.term_of (SShare.encode N kex); other])⌝ ∧
  SShare.wf kex ∧
  session (N.@"sess") Resp (SShare.cnonce kex) (SShare.snonce kex)
          (SShare.meth_of kex, SShare.session_key_of N kex, other).

Definition ctx : iProp :=
  Keys.ctx N ∧
  enc_pred (N.@"server_hello") hello_pred ∧
  enc_pred (N.@"server_hello_sig") hello_sig_pred ∧
  session_ctx (N.@"sess") P.

Lemma ctx_alloc (E E' : coPset) :
  ↑N.@"server_hello" ⊆ E →
  ↑N.@"server_hello_sig" ⊆ E →
  Keys.ctx N -∗
  session_ctx (N.@"sess") P -∗
  enc_pred_token E ={E'}=∗
  ctx ∗
  enc_pred_token (E ∖ ↑N.@"server_hello" ∖ ↑N.@"server_hello_sig").
Proof.
iIntros "% % #ctx #? tok".
iMod (enc_pred_set (N.@"server_hello") hello_pred with "tok")
  as "[#? tok]"; eauto.
iMod (enc_pred_set (N.@"server_hello_sig") hello_sig_pred with "tok")
  as "[#? tok]"; try solve_ndisj.
iModIntro; do !iSplit => //.
Qed.

Definition wf sp : iProp :=
  SShare.wf (share sp) ∧
  pterm (TKey Dec (verif_key sp)) ∧
  pterm (other sp).

#[global]
Instance wf_persistent sp : Persistent (wf sp).
Proof. apply _. Qed.

Lemma pterm_hello E sp :
  ↑N ⊆ E →
  let ss := share sp in
  ctx -∗
  wf sp -∗
  nonce_meta_token (SShare.snonce ss) (↑N.@"sess") -∗
  P Resp (SShare.cnonce ss) (SShare.snonce ss)
    (SShare.meth_of ss, SShare.session_key_of N ss, other sp) ={E}=∗
  pterm (hello N sp) ∗
  session (N.@"sess") Resp (SShare.cnonce ss) (SShare.snonce ss)
    (SShare.meth_of ss, SShare.session_key_of N ss, other sp) ∗
  waiting_for_peer (N.@"sess") P Resp (SShare.cnonce ss) (SShare.snonce ss)
    (SShare.meth_of ss, SShare.session_key_of N ss, other sp).
Proof.
iIntros (?) "#(keys & hello_ctx & sig_ctx & sess_ctx)".
iIntros "#(wf_share & p_vkey & p_other) token r".
iMod (session_begin with "sess_ctx r [token]") as "[#sess close]".
- solve_ndisj.
- by eauto.
iFrame; iModIntro; rewrite pterm_of_list /=; do !iSplit=> //.
  rewrite pterm_of_list /=; do !iSplit => //.
  by iApply SShare.pterm_encode; eauto.
iAssert (sterm (TKey Dec (verif_key sp))) as "s_vkey".
  by iApply pterm_sterm.
rewrite sterm_TKey.
iApply pterm_TEncIS; eauto.
- by rewrite sterm_TKey; iApply SShare.sterm_session_key_of.
- by iModIntro; iExists sp; eauto.
- rewrite sterm_of_list /= sterm_TEnc sterm_tag sterm_THash sterm_of_list /=.
  rewrite sterm_TKey.
  do !iSplit => //.
  + iApply pterm_sterm. by iApply SShare.pterm_encode.
  + by iApply pterm_sterm.
iIntros "!> #fail"; rewrite pterm_of_list /=.
do !iSplit => //.
iApply pterm_TEncIS; eauto.
- by rewrite sterm_TKey.
- iModIntro. iExists (share sp), (other sp); by do !iSplit => //.
- rewrite sterm_THash sterm_of_list /=; do !iSplit => //.
  + by iApply pterm_sterm; iApply SShare.pterm_encode.
  + by iApply pterm_sterm.
iIntros "!> _"; rewrite pterm_THash; iLeft.
rewrite pterm_of_list /=; do !iSplit => //.
by iApply SShare.pterm_encode.
Qed.

(* TODO: Clean this statement *)
Lemma pterm_checkE cp sh vkey s_ke :
  check N cp sh = Some (vkey, s_ke) →
  ctx -∗
  pterm sh -∗
  ∃ k, ⌜vkey = TKey Dec k⌝ ∧
       ⌜CParams.share cp = SShare.cshare_of s_ke⌝ ∧
       sterm k ∧
       pterm (SShare.cnonce s_ke) ∧
       pterm (SShare.snonce s_ke) ∧
       sterm (SShare.session_key_of' N s_ke) ∧
       ⌜∀ sp, sh = hello N sp →
              SShare.cnonce (share sp) = SShare.cnonce s_ke ∧
              SShare.snonce (share sp) = SShare.snonce s_ke ∧
              SShare.session_key_of N (share sp) = SShare.session_key_of' N s_ke ∧
              verif_key sp = k ∧
              SShare.encode' N s_ke = SShare.encode N (share sp) ∧
              SShare.meth_of s_ke = SShare.meth_of (share sp) ∧
              other sp = CParams.other cp⌝ ∧
       ▷ (pterm (TKey Enc k) ∧
            pterm (TKey Enc (SShare.session_key_of' N s_ke)) ∨
          ∃ sp, ⌜sh = hello N sp⌝ ∧
                SShare.wf (share sp) ∧
                session (N.@"sess") Resp
                        (SShare.cnonce s_ke)
                        (SShare.snonce s_ke)
                        (SShare.meth_of s_ke,
                         SShare.session_key_of' N s_ke, CParams.other cp)).
Proof.
rewrite /check; case: Spec.to_listP => //= {}sh.
elim/(@list_len_rect 2): sh => [pub sig|sh ne]; last first.
  by rewrite prod_of_list_neq.
rewrite unlock /=; case: Spec.to_listP => //= {}pub.
elim/(@list_len_rect 2): pub => [kex other'|pub ne]; last first.
  by rewrite prod_of_list_neq.
rewrite unlock /=.
case e_check: SShare.check => [kex'|] //=.
move/SShare.pterm_checkE: e_check; move: kex' => {}kex [e_cp ->].
case e_dec: Spec.tdec => [res|] //=.
move/Spec.tdecK: e_dec=> -> {sig}.
case: Spec.to_listP => //= {}res.
elim/(@list_len_rect 2): res => [verif_key sig|res neq]; last first.
  by rewrite prod_of_list_neq.
rewrite [prod_of_list _ _]unlock /=.
case: decide => [-> {other'}|//] /=.
rewrite /verify /Spec.tdec /Spec.dec.
case: verif_key => //= - [] //= verif_key.
case: sig => //= ? sig.
case: decide => [<-|//] /=.
case: Spec.untagP=> [ {}sig ->|//=].
rewrite bool_decide_decide; case: decide => [->|//] [] {s_ke} <- <-.
do !rewrite pterm_of_list /=.
iIntros "#(? & ctx1 & ctx2 & _)".
iDestruct 1 as "# ((p_kex & p_cp & _) & p_sig & _)".
iPoseProof (pterm_sterm with "p_sig") as "s_sig".
iExists verif_key; do 3!iSplit => //.
  rewrite sterm_TEnc sterm_tag sterm_of_list /= sterm_TKey.
  by iDestruct "s_sig" as "[_ [??]]".
iSplit.
  by rewrite -(SShare.cnonce_encode' N); iApply SShare.pterm_cnonce.
iSplit.
  by rewrite -(SShare.snonce_encode' N); iApply SShare.pterm_snonce.
iSplit.
  rewrite sterm_TEnc sterm_tag.
  by iDestruct "s_sig" as "[??] {p_sig}".
iSplit.
  iPureIntro.
  move=> sp /Spec.of_list_inj [].
  case/Spec.of_list_inj=> /SShare.term_of_inj.
  case/SShare.encode_eq=> [] -> [] -> [] -> [] _ [] _ ? -> ?.
  case/Spec.tag_inj=> _ /Spec.of_list_inj [-> _].
  case/Spec.tag_inj=> _ [] /Spec.of_list_inj [/SShare.term_of_inj ->].
  by eauto.
iClear "s_sig".
iPoseProof (pterm_TEncE with "p_sig ctx1") as "[[psk_fail pub]|hello]".
- rewrite pterm_of_list /=.
  iDestruct "pub" as "{p_sig} (p_vkey & p_sig & _)".
  iPoseProof (pterm_TEncE with "p_sig ctx2") as "[[??]|hello]"; eauto.
  iDestruct "hello" as "(#hello & s_sig & _)"; iModIntro.
  iDestruct "hello" as (kex' other') "(%e_hash & wf & hello)".
  case: e_hash => /Spec.of_list_inj [/SShare.term_of_inj e_kex <- {other'}].
  iRight.
  iExists (Params kex' verif_key (CParams.other cp)); iSplit.
    iPureIntro.
    rewrite e_kex; by case/SShare.encode_eq: e_kex => [_ [] _ [] ->].
  iSplit => //.
  by case/SShare.encode_eq: e_kex => [-> [] -> [] -> [] _ [] _ ->]; eauto.
- iDestruct "hello" as "(#hello & _ & _)".
  iModIntro.
  iDestruct "hello" as (sp) "(%e & wf & hello)".
  case/Spec.of_list_inj: e => -> _ /Spec.tag_inj [] _ [].
  case/Spec.of_list_inj=> [/SShare.term_of_inj e_ke ->].
  iRight.
  iExists sp; iSplit.
    iPureIntro.
    by rewrite e_ke; case/SShare.encode_eq: e_ke => [_ [] _ [] ->].
  by case/SShare.encode_eq: e_ke => -> [] -> [] -> [] _ [] _ ->; eauto.
Qed.

End Proofs.

End SParams.

Coercion SParams.term_of : SParams.t >-> term.

Section Protocol.

Context `{!heapGS Σ, !cryptisG Σ}.
Context `{S : !sessionG Σ}.
Notation iProp := (iProp Σ).
Variable N : namespace.

Implicit Types t : term.
Implicit Types rl : role.
Implicit Types Φ : val → iProp.

Definition P rl t1 t2 (x : Meth.t * term * term) : iProp := True.

Definition tls_client : val := λ: "c" "kex" "other",
  let: "kex" := CShare.I.new "kex" in
  let: "cp"  := term_of_list ["kex"; "other"] in
  let: "ch"  := CParams.I.hello N "cp" in
  send "c" "ch";;
  let: "sh" := recv "c" in
  bind: "res" := SParams.I.check N "cp" "sh" in
  let: "vkey" := Fst "res" in
  let: "kex" := Snd "res" in
  let: "session_key" := SShare.I.session_key_of' N "kex" in
  let: "sk" := mkkey "session_key" in
  let: "ack" := tenc (N.@"ack") (Fst "sk") "sh" in
  send "c" "ack" ;;
  SOME ("vkey", SShare.I.cnonce "kex", SShare.I.snonce "kex", "session_key").

Definition ack_pred (k t : term) : iProp :=
  ∀ sp, ⌜t = SParams.hello N sp⌝ →
  let ss := SParams.share sp in
  let m  := SShare.meth_of ss in
  let sk := SShare.session_key_of N ss in
  session (N.@"sess") Init
          (SShare.cnonce ss) (SShare.snonce ss) (m, sk, SParams.other sp) ∧
  ∃ ke, ⌜SShare.encode' N ke = SShare.encode N ss⌝ ∧
        CShare.wf (SShare.cshare_of ke).

Definition tls_ctx : iProp :=
  Keys.ctx N ∧
  CParams.ctx N ∧
  SParams.ctx N P ∧
  enc_pred (N.@"ack") ack_pred ∧
  session_ctx (N.@"sess") P.

Lemma tls_ctx_alloc E1 E2 E3 E4 E' :
  ↑N ⊆ E1 →
  ↑N ⊆ E2 →
  ↑N ⊆ E3 →
  ↑N ⊆ E4 →
  nown_token session_name E1 -∗
  enc_pred_token E2 -∗
  hash_pred_token E3 -∗
  key_pred_token E4 ={E'}=∗
  tls_ctx ∗
  nown_token session_name (E1 ∖ ↑N) ∗
  enc_pred_token (E2 ∖ ↑N) ∗
  hash_pred_token (E3 ∖ ↑N) ∗
  key_pred_token (E4 ∖ ↑N).
Proof.
iIntros (????) "nown_tok enc_tok hash_tok key_tok".
iMod (Keys.ctx_alloc with "hash_tok key_tok")
  as "(#kctx & hash_tok & key_tok)"; try solve_ndisj.
iMod (session_alloc (N.@"sess") P with "nown_tok")
  as "[#sess nown_tok]"; try solve_ndisj.
iMod (CParams.ctx_alloc with "kctx hash_tok")
  as "[#cctx hash_tok]"; first solve_ndisj.
iMod (SParams.ctx_alloc with "kctx sess enc_tok") as "[#? enc_tok]";
  try solve_ndisj.
iMod (enc_pred_set (N.@"ack") ack_pred with "enc_tok") as "[#? enc_tok]";
  try solve_ndisj.
iModIntro.
iSplit.
  do !iSplit => //.
iSplitL "nown_tok".
  iApply nown_token_drop; last eauto; solve_ndisj.
iSplitL "enc_tok".
  iApply enc_pred_token_drop; last eauto; solve_ndisj.
iSplitL "hash_tok".
  iApply hash_pred_token_drop; last eauto; solve_ndisj.
iApply key_pred_token_drop; last eauto; solve_ndisj.
Qed.

Lemma wp_tls_client c ke other E Φ :
  ↑cryptisN ⊆ E →
  ↑N ⊆ E →
  channel c -∗
  tls_ctx -∗
  Meth.wf ke -∗
  pterm other -∗
  (∀ res,
      match res with
      | Some (vkey, cn, sn, sk) =>
        ∃ k, ⌜vkey = TKey Dec k⌝ ∧
             sterm k ∧
             pterm cn ∧
             pterm sn ∧
             sterm sk ∧
             session (N.@"sess") Init cn sn (ke, sk, other) ∧
             ▷ (pterm (TKey Enc k) ∧ pterm (Meth.psk ke) ∨
                session (N.@"sess") Resp cn sn (ke, sk, other) ∧
                □ ∀ kt, pterm (TKey kt sk) -∗
                ◇ if Meth.has_dh ke then False else pterm (Meth.psk ke))
      | None => True
      end -∗
      Φ (repr res)) -∗
  WP tls_client c ke other @ E {{ Φ }}.
Proof.
iIntros (? sub) "#? #(k_ctx & c_ctx & s_ctx & ackP & sess_ctx) #p_ke #p_other post".
rewrite /tls_client; wp_pures.
wp_bind (CShare.I.new _); iApply (CShare.wp_new _) => //.
iIntros (ke' e) "#p_ke' token"; wp_pures.
rewrite (term_meta_token_difference _ (↑N.@"binder")); try set_solver.
iDestruct "token" as "[binder token]".
pose cp := {| CParams.share := ke'; CParams.other := other |}.
iMod (CParams.wf_set _ cp with "p_ke' binder p_other") as "#wf_cp".
rewrite (term_meta_token_difference _ (↑N.@"sess")); try solve_ndisj.
iDestruct "token" as "[sess token]".
wp_list; wp_term_of_list.
wp_pures; wp_bind (CParams.I.hello _ _).
iApply (CParams.wp_hello N cp).
wp_pures; wp_bind (send _ _); iApply wp_send => //.
  by iModIntro; iApply CParams.pterm_hello.
wp_pures; wp_bind (recv _); iApply wp_recv => //.
iIntros (sh) "#p_sh"; wp_pures.
wp_bind (SParams.I.check _ _ _); iApply (SParams.wp_check N cp).
case e_check: SParams.check => [res|]; wp_pures; last by iApply ("post" $! None).
case: res=> vkey ke'' in e_check *.
iDestruct (SParams.pterm_checkE with "s_ctx p_sh") as (k) "Hk"; eauto.
iDestruct "Hk" as "/= (%e_k & %e_share & #s_k & #p_cn & #p_sn &
                       #s_sk & %e_hello & rest)".
subst ke' vkey; rewrite SShare.cnonce_cshare_of.
iMod (session_begin _ Init (SShare.cnonce ke'') (SShare.snonce ke'')
                    (SShare.meth_of ke'', SShare.session_key_of' N ke'',
                     CParams.other cp)
        with "sess_ctx [] sess") as "[#sess close]".
- solve_ndisj.
- by eauto.
wp_bind (SShare.I.session_key_of' _ _); iApply SShare.wp_session_key_of'; wp_pures.
wp_bind (mkkey _); iApply wp_mkkey; wp_pures => /=.
wp_tenc => /=; wp_pures.
iDestruct "rest" as "[[fail_vsk fail_psk]|succ]".
  iPoseProof (SShare.pterm_session_key_of' with "k_ctx fail_psk") as ">fail".
  wp_bind (send _ _); iApply wp_send => //.
  iModIntro.
  iApply pterm_TEncIS; eauto.
  - by rewrite sterm_TKey.
  - iIntros "!> %sp %e_sh".
    by case: (e_hello _ e_sh) => [] -> [] -> [] -> [] _ [] e_enc [] <- ->; eauto.
  - by iApply pterm_sterm.
  wp_pures; wp_bind (SShare.I.snonce _); iApply SShare.wp_snonce.
  wp_pures; wp_bind (SShare.I.cnonce _); iApply SShare.wp_cnonce.
  wp_pures.
  iApply ("post" $! (Some (_, _, _, _))).
  rewrite e CShare.psk_meth_of.
  by iModIntro; iExists _; do 6!iSplit => //; eauto.
wp_bind (send _ _); iApply wp_send => //.
  iModIntro.
  iApply pterm_TEncIS; eauto; first by rewrite sterm_TKey.
  - iIntros "!> %sp %e_sp".
    by case: (e_hello _ e_sp) => -> [] -> [] -> [] _ [] e_enc [] <- ->; eauto.
  - by iApply pterm_sterm.
iDestruct "succ" as (sp) "(-> & wf & succ)".
wp_pures; wp_bind (SShare.I.snonce _); iApply SShare.wp_snonce.
wp_pures; wp_bind (SShare.I.cnonce _); iApply SShare.wp_cnonce.
wp_pures.
iApply ("post" $! (Some (_, _, _, _))) => //.
rewrite e.
iModIntro; iExists _; do 6!iSplit => //.
case: (e_hello _ eq_refl) => ? [] ? [] e_sk [] ? [] ? [] ? ?.
iModIntro; iRight; iSplit => //.
iIntros (kt); rewrite -e_sk.
iModIntro.
iApply SShare.pterm_session_key_of => //.
Qed.

Definition tls_server : val := λ: "c" "psk" "g" "verif_key" "other",
  let: "ch" := recv "c" in
  bind: "ke" := CParams.I.check N "psk" "g" "other" "ch" in
  let: "ke'" := SShare.I.new "ke" in
  let: "sp"  := term_of_list ["ke'"; "verif_key"; "other"] in
  let: "sh"  := SParams.I.hello N "sp" in
  send "c" "sh" ;;
  let: "session_key" := SShare.I.session_key_of N "ke'" in
  let: "sk" := mkkey "session_key" in
  let: "ack" := recv "c" in
  bind: "ack" := tdec (N.@"ack") (Snd "sk") "ack" in
  assert: eq_term "ack" "sh" in
  SOME "ke'".

Lemma wp_tls_server c psk g verif_key other E Φ :
  ↑cryptisN ⊆ E →
  ↑N ⊆ E →
  channel c -∗
  tls_ctx -∗
  sterm psk -∗
  pterm g -∗
  sterm (TKey Enc verif_key) -∗
  pterm (TKey Dec verif_key) -∗
  pterm other -∗
  (∀ ke : option SShare.t,
      match ke with
      | Some ke =>
        pterm (SShare.cnonce ke) ∧
        pterm (SShare.snonce ke) ∧
        sterm (SShare.session_key_of N ke) ∧
        session (N.@"sess") Resp (SShare.cnonce ke) (SShare.snonce ke)
                (SShare.meth_of ke, SShare.session_key_of N ke, other) ∧
        ▷ (pterm (SShare.psk ke) ∨
           session (N.@"sess") Init (SShare.cnonce ke) (SShare.snonce ke)
                   (SShare.meth_of ke, SShare.session_key_of N ke, other) ∧
           □ ∀ kt, pterm (TKey kt (SShare.session_key_of N ke)) -∗
           ◇ if SShare.has_dh ke then False else pterm (SShare.psk ke))
      | None => True
      end -∗ Φ (repr (SShare.term_of <$> ke))) -∗
  WP tls_server c psk g verif_key other @ E {{ Φ }}.
Proof.
iIntros (? sub) "#? #(k_ctx & c_ctx & s_ctx & ? & sess_ctx)".
iIntros "#s_psk #p_g #s_sign #s_verif #p_other post".
rewrite /tls_server; wp_pures.
wp_bind (recv _); iApply wp_recv => //.
iIntros (ch) "#p_ch"; wp_pures.
wp_bind (CParams.I.check _ _ _ _ _).
iApply CParams.wp_check.
case e: CParams.check => [ke|] //=; wp_pures; last first.
  by iApply ("post" $! None).
iDestruct (CParams.pterm_checkE e with "c_ctx p_ch")
  as "{p_ch} (%compat & p_ke & p_ch)".
wp_bind (SShare.I.new _); iApply SShare.wp_new; eauto.
iIntros (ke') "-> #p_ke' token"; wp_pures.
wp_list; wp_term_of_list.
pose sp := SParams.Params ke' verif_key other.
iAssert (SParams.wf sp) as "wf_sp"; first by do !iSplit => //.
wp_pures.
wp_bind (SParams.I.hello _ _); iApply (SParams.wp_hello _ sp).
rewrite (term_meta_token_difference _ (↑N.@"sess")); eauto.
iDestruct "token" as "[token _]".
iMod (SParams.pterm_hello with "s_ctx wf_sp token []")
  as "(#p_hello & #sess & close)" => //.
wp_pures; wp_bind (send _ _); iApply wp_send; eauto.
wp_pures.
wp_bind (SShare.I.session_key_of _ _); iApply SShare.wp_session_key_of.
wp_pures.
wp_bind (mkkey _); iApply wp_mkkey; wp_pures.
wp_bind (recv _); iApply wp_recv => //; iIntros (ack) "#p_ack"; wp_pures.
wp_tdec_eq ack' e_ack; wp_pures; last by iApply ("post" $! None).
rewrite {}e_ack; wp_eq_term e_ack; last by wp_pures; iApply ("post" $! None).
rewrite {}e_ack; wp_pures; iApply ("post" $! (Some ke')).
iModIntro; iSplit.
  rewrite -(SShare.cnonce_encode N).
  iApply SShare.pterm_cnonce.
  by iApply SShare.pterm_encode => //.
iSplit.
  rewrite -(SShare.snonce_encode N).
  iApply SShare.pterm_snonce.
  by iApply SShare.pterm_encode => //.
iSplit.
  iPoseProof (pterm_sterm with "p_ack") as "{p_ack} ack".
  by rewrite sterm_TEnc; iDestruct "ack" as "[sk _]".
iDestruct "p_ch" as "[p_ch|p_ch]"; first by eauto.
rewrite pterm_TEnc; iSplit => //.
iDestruct "p_ack" as "[[fail _]|(_ & succ & decl)]".
  iMod (SShare.pterm_session_key_ofW with "k_ctx p_ke' fail") as "?".
  by eauto.
iPoseProof (wf_enc_elim with "succ []") as "{succ} #succ"; eauto.
iModIntro.
iDestruct ("succ" $! sp with "[//]") as "{succ} [sess' succ]".
iRight; iSplitL => //.
iIntros "!> %kt #p_sk".
iDestruct "succ" as (ke) "[%e_enc wf]".
iPoseProof (SShare.pterm_session_key_of kt e_enc with "k_ctx [] p_ke' p_sk")
  as "?" => //.
by case/SShare.encode_eq: e_enc => _ [] _ [] _ [] -> [] -> ?.
Qed.

End Protocol.

Arguments tls_ctx_alloc {Σ _ _ _} N E1 E2 E3 E4 E'.
