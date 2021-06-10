(*

Transcribed from https://github.com/Inria-Prosecco/reftls

*)


From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl namespace_map frac.
From iris.base_logic.lib Require Import auth.
From iris.heap_lang Require Import notation proofmode.
From crypto Require Import lib guarded term crypto primitives tactics session.
From crypto Require Import dh.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* MOVE *)
Definition opterm `{!heapG Σ, !cryptoG Σ} (ot : option term) : iProp Σ :=
  match ot with
  | Some t => pterm t
  | None => True
  end.

Global Instance persistent_opterm `{!heapG Σ, !cryptoG Σ} ot :
  Persistent (opterm ot).
Proof. apply _. Qed.
(* /MOVE *)

Module AEAD.

(* FIXME This does not work if we inline "h" *)
Definition enc (N : namespace) : val := λ: "k" "ad" "payload",
  let: "h" := hash "ad" in
  bind: "e" := tenc N (Snd "k") (term_of_list ["h"; "payload"]) in
  SOME (term_of_list ["ad"; "e"]).

Definition dec (N : namespace) : val := λ: "k" "m",
  bind: "m" := list_of_term "m" in
  list_match: ["ad"; "e"] := "m" in
  let: "h" := hash "ad" in
  bind: "dec_e" := tdec N (Fst "k") "e" in
  bind: "dec_e" := list_of_term "dec_e" in
  list_match: ["h'"; "payload"] := "dec_e" in
  assert: eq_term "h'" "h" in
  SOME ("ad", "payload").

Section Lemmas.

Context `{!heapG Σ, !cryptoG Σ}.

Variable N : namespace.

Variable P : term → term → iProp Σ.

Implicit Types k t ad payload : term.
Implicit Types Φ : val → iProp Σ.

Definition inv k t : iProp Σ :=
  ∃ ad payload, ⌜t = Spec.of_list [THash ad; payload]⌝ ∧ P ad payload.

Definition ctx := enc_pred N inv.

Lemma wp_enc E Φ k ad payload :
  ctx -∗
  □ P ad payload -∗
  sterm (TKey Enc k) -∗
  pterm ad -∗
  sterm payload -∗
  □ (pterm (TKey Dec k) → pterm payload) -∗
  (∀ t, pterm t -∗ Φ (SOMEV t)) -∗
  WP enc N (TKey Dec k, TKey Enc k) ad payload @ E {{ Φ }}.
Proof.
iIntros "#ctx #Pd #s_k #p_ad #s_payload #p_payload post".
rewrite /enc; wp_hash.
wp_list; wp_term_of_list.
wp_tenc; wp_list; wp_term_of_list.
wp_pures; iApply "post".
rewrite pterm_of_list /=; do !iSplit => //.
iApply pterm_TEncIS => //.
- by iModIntro; iExists _, _; eauto.
- by rewrite sterm_of_list /= sterm_THash -[sterm ad]pterm_sterm; eauto.
iIntros "!> #p_k"; rewrite pterm_of_list /= pterm_THash.
by do !iSplit => //; eauto; iApply "p_payload".
Qed.

Ltac failure :=
  wp_pures; iApply "post_none".

Definition corruption k : iProp Σ :=
  pterm (TKey Dec k) ∨ pterm (TKey Enc k).

Lemma wp_dec E Φ k t :
  ctx -∗
  pterm t -∗
  (∀ ad payload,
    pterm ad -∗
    sterm payload -∗
    ▷ (corruption k ∨ □ P ad payload) -∗
    Φ (SOMEV (ad, payload))) -∗
  Φ NONEV -∗
  WP dec N (TKey Dec k, TKey Enc k)%V t @ E {{ Φ }}.
Proof.
iIntros "#ctx #p_t post_some post_none".
rewrite /dec; wp_list_of_term_eq ts e; last by failure.
rewrite {t}e.
wp_list_match => [ad m {ts} ->|_]; wp_finish; try by failure.
wp_hash.
rewrite pterm_of_list /=; iDestruct "p_t" as "(p_ad & p_m & _)".
wp_tdec m; last by failure.
wp_list_of_term_eq m' e; last by failure.
wp_pures; rewrite {m}e.
wp_list_match => [h' payload {m'} ->|_] /=; wp_finish; try by failure.
wp_eq_term e; last by failure.
subst h'.
iDestruct (pterm_TEncE with "p_m ctx") as "[[fail pub]|sec]".
  wp_pures; iApply "post_some"; rewrite /corruption; eauto.
  iApply pterm_sterm.
  by rewrite pterm_of_list /=; iDestruct "pub" as "(_ & ? & _)".
iDestruct "sec" as "# (#inv & sec & _)".
wp_if.
iDestruct "inv" as (ad' payload') "(%e & ?)".
case/Spec.of_list_inj: e => <- <-.
rewrite sterm_of_list /=; iDestruct "sec" as "(_ & ? & _)".
by wp_pures; iApply "post_some"; eauto.
Qed.

End Lemmas.

End AEAD.

Module Keys.

Section Keys.

Context `{!heapG Σ, cryptoG Σ}.
Notation iProp := (iProp Σ).

Implicit Types t : term.
Implicit Types Φ : val → iProp.

Definition dh_key_pred N (kt : key_type) (t : term) : iProp :=
  ∃ g a b psk vsk : term,
    ⌜t = TExp g [a; b]⌝ ∧
    dh_meta (TExp g [a]) (N.@"owner") psk ∧ pterm psk ∧
    dh_meta (TExp g [b]) (N.@"owner") vsk ∧ pterm vsk.

Definition ctx N : iProp :=
  hash_pred (N.@"psk") (λ _, True)%I ∧
  key_pred (N.@"sess_key") (λ _ _, False)%I.

Global Instance ctx_persistent N : Persistent (ctx N).
Proof. apply _. Qed.

End Keys.

End Keys.

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

Definition psk ke :=
  match ke with
  | Psk psk => psk
  | Dh _ => Spec.zero
  | PskDh psk _ => psk
  end.

Definition has_dh ke :=
  match ke with Psk _ => false | _ => true end.

Module I.

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

Context `{!heapG Σ, cryptoG Σ}.
Notation iProp := (iProp Σ).

Implicit Types t : term.
Implicit Types Φ : val → iProp.

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

Definition encode N ke :=
  match ke with
  | Psk psk cn => Psk (THash (Spec.tag (N.@"psk") psk)) cn
  | Dh g cn x => Dh g cn (TExp g [x])
  | PskDh psk g cn x => PskDh (THash (Spec.tag (N.@"psk") psk)) g cn (TExp g [x])
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

(** The pre-shared key associated with a share.  This is zero if no pre-shared
key is being used. *)

Definition psk ke :=
  match ke with
  | Psk psk _ => psk
  | Dh _ _ _ => Spec.zero
  | PskDh psk _ _ _ => psk
  end.

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

Context `{!heapG Σ, cryptoG Σ}.
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

Definition wf N ke : iProp :=
  match ke with
  | Psk psk cn =>
    sterm psk ∧ pterm cn
  | Dh g cn x  =>
    pterm g ∧ pterm cn ∧ dh_seed (λ _, True)%I x ∧
    dh_meta (TExp g [x]) (N.@"owner") Spec.zero
  | PskDh psk g cn x =>
    sterm psk ∧
    pterm g ∧ pterm cn ∧ dh_seed (λ _, True)%I x ∧
    dh_meta (TExp g [x]) (N.@"owner") psk
  end.

Instance Persistent_wf N ke : Persistent (wf N ke).
Proof. case: ke => *; apply _. Qed.

Lemma wf_psk N ke : wf N ke -∗ sterm (psk ke).
Proof.
case: ke => [psk ?|???|psk ???] /=.
- by iIntros "(? & ?)".
- by iIntros "_"; rewrite sterm_TInt.
- by iIntros "(? & ? & ? & ?)".
Qed.

Lemma wf_encode N ke :
  Keys.ctx N -∗
  wf N ke -∗
  pterm (term_of (encode N ke)).
Proof.
iIntros "#(hash & _) #wf".
case: ke => [psk cn|g cn x|psk g cn x] //=.
- iDestruct "wf" as "[??]".
  rewrite pterm_tag pterm_of_list /=; do !iSplit => //.
  rewrite pterm_THash sterm_tag; iRight; iSplit => //.
  by iExists _, _, _; eauto.
- iDestruct "wf" as "(? & ? & ? & ?)".
  rewrite pterm_tag pterm_of_list /=.
  do !iSplit => //.
  iApply dh_pterm_TExp; eauto.
  by iApply pterm_sterm.
- iDestruct "wf" as "(? & ? & ? & ? & ?)".
  rewrite pterm_tag pterm_of_list /=.
  do !iSplit => //.
    rewrite pterm_THash sterm_tag; iRight; iSplit => //.
    by iExists _, _, _; eauto.
  by iApply dh_pterm_TExp; eauto; iApply pterm_sterm.
Qed.

Lemma wp_new N ke E Φ :
  Meth.wf ke -∗
  (∀ ke', ⌜ke = meth_of ke'⌝ -∗
          wf N ke' -∗
          nonce_meta_token (cnonce ke') ⊤ -∗
          Φ (term_of ke')) -∗
  WP I.new ke @ E {{ Φ }}.
Proof.
iIntros "#p_ke post"; rewrite /I.new; wp_pures.
iApply Meth.wp_case; case: ke => [psk|g|psk g]; wp_pures.
- wp_bind (mknonce _); iApply (wp_mknonce _ True%I (λ _, True)%I).
  iIntros (cn) "_ #p_cn _ token"; wp_list; wp_term_of_list.
  wp_tag.
  iApply ("post" $! (Psk psk cn) with "[] [] token") => //=.
  do !iSplit => //.
  by iApply "p_cn".
- wp_bind (mkdh _); iApply (wp_mkdh (λ _, True)%I g).
  iIntros (a) "_ #p_a token"; wp_list.
  rewrite (term_meta_token_difference _ (↑N.@"owner")); try set_solver.
  iDestruct "token" as "[owner _]".
  iMod (term_meta_set _ _ Spec.zero with "owner") as "#owner"; eauto.
  wp_bind (mknonce _); iApply (wp_mknonce _ True%I (λ _, True)%I).
  iIntros (cn) "_ #p_cn _ token"; wp_list; wp_term_of_list.
  wp_tag.
  rewrite (term_meta_token_difference _ ⊤); try set_solver.
  iDestruct "token" as "[token _]".
  iApply ("post" $! (Dh g cn a)) => //=.
  do !iSplit => //.
  by iApply "p_cn".
- wp_bind (mkdh _); iApply (wp_mkdh (λ _, True)%I g).
  iIntros (a) "_ #p_a token"; wp_list.
  rewrite (term_meta_token_difference _ (↑N.@"owner")); try set_solver.
  iDestruct "token" as "[owner _]".
  iMod (term_meta_set _ _ psk with "owner") as "#owner"; eauto.
  wp_bind (mknonce _); iApply (wp_mknonce _ True%I (λ _, True)%I).
  iIntros (cn) "_ #p_cn _ token"; wp_list; wp_term_of_list.
  wp_tag.
  iApply ("post" $! (PskDh psk g cn a)) => //=.
  iDestruct "p_ke" as "(? & ?)".
  do !iSplit => //.
  by iApply "p_cn".
Qed.

End Proofs.

End CShare.

Coercion CShare.term_of : CShare.t >-> term.
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

Lemma cnonce_encode' N ke : cnonce (encode' N ke) = cnonce ke.
Proof. by case: ke. Qed.

Lemma snonce_encode' N ke : snonce (encode' N ke) = snonce ke.
Proof. by case: ke. Qed.

Definition psk ke := CShare.psk (cshare_of ke).

(** Compute the session key given the pre-shared key used by the server and its
key share. *)

Definition session_key_of N ke :=
  match ke with
  | Psk psk cn sn =>
    Spec.tag (N.@"sess_key")
             (Spec.of_list [psk; cn; sn])
  | Dh _ _ _ gx y =>
    Spec.tag (N.@"sess_key") (Spec.texp gx y)
  | PskDh psk _ _ _ gx y =>
    Spec.tag (N.@"sess_key") (Spec.of_list [psk; Spec.texp gx y])
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

Context `{!heapG Σ, cryptoG Σ}.
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
  by wp_list; wp_pures.
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
  by wp_list; wp_pures.
Qed.

Definition wf N (vsk : term) ke : iProp :=
  match ke with
  | Psk psk c_nonce s_nonce =>
    sterm psk ∧ pterm c_nonce ∧ pterm s_nonce
  | Dh g cn sn gx y =>
    pterm g ∧ pterm cn ∧ pterm sn ∧ pterm gx ∧
    dh_seed (λ _, True)%I y ∧
    dh_meta (TExp g [y]) (N.@"owner") vsk
  | PskDh psk g cn sn gx y =>
    sterm psk ∧
    pterm g ∧ pterm cn ∧ pterm sn ∧
    pterm gx ∧
    dh_seed (λ _, True)%I y ∧
    dh_meta (TExp g [y]) (N.@"owner") vsk
  end.

Instance Persistent_wf N vsk ke : Persistent (wf N vsk ke).
Proof. case: ke => *; apply _. Qed.

(* TODO: strengthen *)
Lemma wp_new N vsk psk g (ke ke' : CShare.t) E Φ :
  CShare.check N psk g ke = Some ke' →
  sterm psk -∗
  pterm g -∗
  pterm ke -∗
  (∀ ke'',
      ⌜ke' = cshare_of ke''⌝ -∗
      wf N vsk ke'' -∗
      nonce_meta_token (snonce ke'') ⊤ -∗
      Φ (term_of ke'')) -∗
  WP I.new ke' @ E {{ Φ }}.
Proof.
iIntros (e_check) "#s_psk #p_g #p_ke post"; rewrite /I.new; wp_pures.
iApply CShare.wp_case.
case: ke => [psk' cn|g' cn gx|psk' g' cn gx] /= in e_check *; wp_pures.
- case: decide e_check => [->|//] [<-] {ke'}.
  wp_pures.
  wp_bind (mknonce _); iApply (wp_mknonce _ True%I (λ _, True)%I).
  iIntros (a) "_ #pred_a _ token"; wp_list; wp_term_of_list.
  wp_tag; wp_pures.
  iApply ("post" $! (Psk _ _ a)) => //=.
  rewrite pterm_tag pterm_of_list /=.
  iDestruct "p_ke" as "(_ & p_cn & _)".
  do !iSplit => //.
  by iApply "pred_a".
- case: decide e_check => [->|//] [<-] {ke'}.
  wp_pures.
  wp_bind (mkdh _); iApply (wp_mkdh (λ _, True)%I g).
  iIntros (a) "_ #pred_a token"; wp_list.
  rewrite (term_meta_token_difference _ (↑N.@"owner")); try set_solver.
  iDestruct "token" as "[owner _]".
  iMod (term_meta_set _ _ vsk with "owner") as "#owner"; eauto.
  wp_bind (mknonce _); iApply (wp_mknonce _ True%I (λ _, True)%I).
  iIntros (sn) "_ #p_sn _ token"; wp_list; wp_term_of_list.
  wp_tag; wp_pures.
  iApply ("post" $! (Dh g cn sn gx a)) => //=.
  rewrite !pterm_tag !pterm_of_list /=.
  iDestruct "p_ke" as "(? & ? & ? & _)".
  do !iSplit => //.
  by iApply "p_sn".
- case: decide e_check => [[-> ->]|//] [<-] {ke'}; wp_pures.
  wp_bind (mkdh _); iApply (wp_mkdh (λ _, True)%I g).
  iIntros (a) "_ #pred_a token"; wp_list.
  rewrite (term_meta_token_difference _ (↑N.@"owner")); try set_solver.
  iDestruct "token" as "[owner _]".
  iMod (term_meta_set _ _ vsk with "owner") as "#owner"; eauto.
  wp_bind (mknonce _); iApply (wp_mknonce _ True%I (λ _, True)%I).
  iIntros (sn) "_ #p_sn _ token"; wp_list; wp_term_of_list.
  wp_tag; wp_pures.
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

(*
Lemma pterm_session_key N ke ke' :
  encode' N ke = encode N ke' →
  Keys.ctx N -∗
  CShare.wf N (cshare_of ke) -∗
  pterm (TKey Enc (session_key_of' N ke)) -∗
  ▷ pterm (psk ke).
Proof.
case: ke => [psk cn sn|g cn sn x gy|psk g cn sn x gy] //=.
- iIntros "_ (_ & #pskP & _) #meta #p_key".
  rewrite pterm_TKey; iDestruct "p_key" as "[p_key|[_ p_key]]".
  + rewrite pterm_tag pterm_of_list /=.
    by iDestruct "p_key" as "(p_key & ?)".
  + by iMod (wf_key_elim with "p_key pskP") as "[]".
- iIntros "_ (_ & _ & #dhP) #(_ & _ & _ & meta) #p_key".
  by iModIntro; rewrite pterm_TInt.
- case: ke' => //= _ _ _ _ _ y [_ <- _ _ _ ->] /=.
  rewrite Spec.texpA.
  iIntros "(_ & _ & #dhP) #(_ & _ & _ & seed & meta) #p_key".
  rewrite pterm_TKey; iDestruct "p_key" as "[p_key|p_key]".
  + rewrite pterm_tag.
*)

End Proofs.

End SShare.

Coercion SShare.term_of : SShare.t >-> term.
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
  c_ke ← CShare.check N psk g ke;
  let psk := CShare.psk c_ke in
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
  bind: "c_ke" := CShare.I.check N "psk" "g" "ke" in
  let: "psk" := CShare.I.psk "c_ke" in
  let: "mac'" := hash (tag (N.@"binder") (term_of_list ["psk"; "ch"])) in
  if: eq_term "other'" "other" && eq_term "mac'" "mac" then SOME "ke" else NONE.

End I.

Section Proofs.

Context `{!heapG Σ, cryptoG Σ}.
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
  CShare.wf N (share cp) ∧
  nonce_meta (CShare.cnonce (share cp)) (N.@"binder") (other cp) ∧
  pterm (other cp).

Instance wf_persistent N cp : Persistent (wf N cp).
Proof. apply _. Qed.

Lemma wf_set N cp :
  CShare.wf N (share cp) -∗
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
        wf N cp.

Definition ctx N : iProp :=
  Keys.ctx N ∧
  hash_pred (N.@"binder") (binder_inv N).

Instance ctx_persistent N : Persistent (ctx N).
Proof. apply _. Qed.

Lemma pterm_hello N cp : ctx N -∗ wf N cp -∗ pterm (hello N cp).
Proof.
iIntros "#[ctx binder] # (wf_cp & meta & p_cp)".
iAssert (pterm (hello_pub N cp)) as "p_pub".
  rewrite pterm_of_list /=; do !iSplit => //.
  by iApply CShare.wf_encode.
rewrite [pterm (hello _ _)]pterm_of_list /=; do ![iSplit => //].
rewrite pterm_THash; iRight; rewrite sterm_tag sterm_of_list /=.
do !iSplit => //.
- by iApply CShare.wf_psk.
- by iApply pterm_sterm.
iExists _, _, _; do !iSplit => //; eauto.
by iExists cp; iModIntro; do !iSplit => //.
Qed.

End Proofs.

End CParams.

Coercion CParams.term_of : CParams.t >-> term.
Existing Instance CParams.wf_persistent.
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
    bind: "enc" :=
      tenc (N.@"server_hello_sig") (Fst "verif_key") (hash "pub") in
    let: "enc" := term_of_list [Snd "verif_key"; "enc"] in
    let: "session_key" := mkkey (SShare.I.session_key_of N "kex") in
    bind: "enc" := tenc (N.@"server_hello") (Fst "session_key") "enc" in
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

Context `{!heapG Σ, cryptoG Σ}.
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

Context `{!sessionG Σ (term * term) (@nonce_meta _ _) nonce_meta_token}.

Definition hello_pred γ N (k t : term) : iProp := ∃ sp,
  let ss := share sp in
  ⌜t = hello_priv N sp⌝ ∧
  SShare.wf N (TKey Enc (verif_key sp)) ss ∧
  session γ (N.@"sess") Resp (SShare.cnonce ss) (SShare.snonce ss)
          (SShare.session_key_of N ss, other sp).

Definition hello_sig_pred γ N (k t : term) : iProp := ∃ kex other,
  ⌜t = THash (Spec.of_list [SShare.term_of (SShare.encode N kex); other])⌝ ∧
  SShare.wf N (TKey Enc k) kex ∧
  session γ (N.@"sess") Resp (SShare.cnonce kex) (SShare.snonce kex)
          (SShare.session_key_of N kex, other).

Definition ctx γ N : iProp :=
  enc_pred (N.@"server_hello") (hello_pred γ N) ∧
  enc_pred (N.@"server_hello_sig") (hello_sig_pred γ N).

(* MOVE *)
Lemma TExpC2 g t1 t2 : TExp g [t1; t2] = TExp g [t2; t1].
Proof.
suff -> : [t1; t2] ≡ₚ [t2; t1] by [].
exact/Permutation_swap.
Qed.

Lemma encode_eq N kex1 kex2 :
  SShare.encode' N kex1 = SShare.encode N kex2 →
  SShare.cnonce kex1 = SShare.cnonce kex2 ∧
  SShare.snonce kex1 = SShare.snonce kex2 ∧
  SShare.session_key_of' N kex1 = SShare.session_key_of N kex2.
Proof.
case: kex1 kex2 => [???|?????|??????] [???|?????|??????] //=.
- by case=> [/Spec.tag_inj [_ ->] -> ->].
- by case=> e_g -> -> <- ->; rewrite e_g !Spec.texpA TExpC2.
- by case=> [] /Spec.tag_inj [_ ->] e_g -> -> <- ->; rewrite e_g !Spec.texpA TExpC2.
Qed.
(* /MOVE *)

(* TODO: Clean this statement *)
Lemma pterm_checkE γ N cp sh vkey s_ke :
  check N cp sh = Some (vkey, s_ke) →
  ctx γ N -∗
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
              other sp = CParams.other cp⌝ ∧
       ▷ (pterm (TKey Enc k) ∧
            pterm (TKey Enc (SShare.session_key_of' N s_ke)) ∨
          ∃ sp, ⌜sh = hello N sp⌝ ∧
                SShare.wf N (TKey Enc k) (share sp) ∧
                session γ (N.@"sess") Resp
                        (SShare.cnonce s_ke)
                        (SShare.snonce s_ke)
                        (SShare.session_key_of' N s_ke, CParams.other cp)).
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
move/tdecK: e_dec=> -> {sig}.
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
iIntros "#[ctx1 ctx2]".
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
  case/Spec.of_list_inj=> /SShare.term_of_inj/encode_eq [] -> [] -> -> -> ?.
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
    rewrite e_kex; by case/encode_eq: e_kex => [_ [] _ ->].
  by case/encode_eq: e_kex => [-> [] -> ->]; eauto.
- iDestruct "hello" as "(#hello & _ & _)".
  iModIntro.
  iDestruct "hello" as (sp) "(%e & wf & hello)".
  case/Spec.of_list_inj: e => -> _ /Spec.tag_inj [] _ [].
  case/Spec.of_list_inj=> [/SShare.term_of_inj e_ke ->].
  iRight.
  iExists sp; iSplit.
    iPureIntro.
    by rewrite e_ke; case/encode_eq: e_ke => [_ [] _ ->].
  by case/encode_eq: e_ke => -> [] -> ->; eauto.
Qed.

End Proofs.

End SParams.

Coercion SParams.term_of : SParams.t >-> term.

Section Protocol.

Context `{!heapG Σ, !cryptoG Σ, !network Σ}.
Context `{S : !sessionG Σ (term * term) (@nonce_meta _ _) nonce_meta_token}.
Notation iProp := (iProp Σ).

Implicit Types t : term.
Implicit Types rl : role.
Implicit Types Φ : val → iProp.

Definition client N : val := λ: "kex" "other",
  let: "kex" := CShare.I.new "kex" in
  let: "cp"  := term_of_list ["kex"; "other"] in
  let: "ch"  := CParams.I.hello N "cp" in
  send "ch";;
  let: "sh" := recv #() in
  bind: "res" := SParams.I.check N "cp" "sh" in
  let: "vkey" := Fst "res" in
  let: "kex" := Snd "res" in
  let: "session_key" := SShare.I.session_key_of' N "kex" in
  let: "sk" := mkkey "session_key" in
  bind: "ack" := tenc (N.@"ack") (Fst "sk") "sh" in
  send "ack" ;;
  SOME ("vkey", SShare.I.cnonce "kex", SShare.I.snonce "kex", "session_key").

Definition inv rl (nA nB : term) (k : term * term) : iProp :=
  match rl with
  | Init => True%I
  | Resp => True%I
  end.

Definition ack_pred γ N (k t : term) : iProp :=
  ∀ sp, ⌜t = SParams.hello N sp⌝ →
  let ss := SParams.share sp in
        session γ (N.@"sess") Init
                (SShare.cnonce ss)
                (SShare.snonce ss)
                (SShare.session_key_of N ss, SParams.other sp).

Definition ctx γ N : iProp :=
  Keys.ctx N ∧
  CParams.ctx N ∧
  SParams.ctx γ N ∧
  enc_pred (N.@"ack") (ack_pred γ N) ∧
  session_ctx γ (N.@"sess") inv.

Lemma blah N vsk c_kex s_kex kt :
  SShare.encode' N c_kex = SShare.encode N s_kex →
  let m := CShare.meth_of (SShare.cshare_of c_kex) in
  Keys.ctx N -∗
  CShare.wf N (SShare.cshare_of c_kex) -∗
  SShare.wf N vsk s_kex -∗
  pterm (TKey kt (SShare.session_key_of N s_kex)) -∗
  ◇ if Meth.has_dh m then False else pterm (Meth.psk m).
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
  rewrite Spec.texpA.
  iIntros "#(p_g & _ & dh_x & meta_x)".
  iIntros "#(_ & _ & _ & p_gx & dh_y & meta_y)".
  rewrite pterm_TKey pterm_tag; iDestruct 1 as "#[p_k|[_ p_k]]".
  + iMod (dh_seed_elim2 with "dh_y p_k") as "[_ p_x]".
    iMod (dh_seed_elim0 with "dh_x p_x") as "[]".
  + iDestruct (wf_key_elim with "p_k []") as "{p_k} #p_exp"; eauto.
    by iMod "p_exp" as "?".
- case: s_kex => //= _ ? ? ? gx y [] /Spec.tag_inj [_ <-].
  move=> <- _ _ <- e2.
  iIntros "#(_ & _ & _ & dh_x & meta_x)".
  iIntros "#(_ & _ & _ & _ & p_gx & dh_y & meta_y)".
  rewrite Spec.texpA pterm_TKey pterm_tag; iDestruct 1 as "#[p_k|[_ p_k]]".
  + rewrite pterm_of_list /=; iDestruct "p_k" as "(_ & p_k & _)".
    iMod (dh_seed_elim2 with "dh_y p_k") as "[_ p_x]".
    by iMod (dh_seed_elim0 with "dh_x p_x") as "[]".
  + iDestruct (wf_key_elim with "p_k []") as "{p_k} #p_exp"; eauto.
    by iMod "p_exp" as "?".
Qed.

(* MOVE *)
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

Lemma psk_meth_of ke : Meth.psk (CShare.meth_of ke) = CShare.psk ke.
Proof. by case: ke. Qed.
(* /MOVE *)

Lemma wp_client γ N ke other E Φ :
  ↑N ⊆ E →
  ctx γ N -∗
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
             ▷ (pterm (TKey Enc k) ∧ pterm (Meth.psk ke) ∨
                session γ (N.@"sess") Resp cn sn (sk, other) ∧
                □ ∀ kt, pterm (TKey kt sk) -∗
                        ◇ if Meth.has_dh ke then False
                          else pterm (Meth.psk ke))
      | None => True
      end →
      Φ (repr res)) -∗
  WP client N ke other @ E {{ Φ }}.
Proof.
iIntros (sub) "#(k_ctx & c_ctx & s_ctx & ackP & sess_ctx) #p_ke #p_other post".
rewrite /client; wp_pures.
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
wp_pures; wp_bind (send _); iApply wp_send.
  by iModIntro; iApply CParams.pterm_hello.
wp_pures; wp_bind (recv _); iApply wp_recv.
iIntros (sh) "#p_sh"; wp_pures.
wp_bind (SParams.I.check _ _ _); iApply (SParams.wp_check N cp).
case e_check: SParams.check => [res|]; wp_pures; last by iApply ("post" $! None).
case: res=> vkey ke'' in e_check *.
iDestruct (SParams.pterm_checkE with "s_ctx p_sh") as (k) "Hk"; eauto.
iDestruct "Hk" as "/= (%e_k & %e_share & #s_k & #p_cn & #p_sn &
                       #s_sk & %e_hello & rest)".
subst ke' vkey; rewrite SShare.cnonce_cshare_of.
iMod (session_begin _ Init (SShare.cnonce ke'') (SShare.snonce ke'')
                    (SShare.session_key_of' N ke'', CParams.other cp)
        with "sess_ctx [] sess") as "[#sess close]".
- solve_ndisj.
- by eauto.
wp_bind (SShare.I.session_key_of' _ _); iApply SShare.wp_session_key_of'; wp_pures.
wp_bind (mkkey _); iApply wp_mkkey; wp_pures => /=.
wp_tenc => /=; wp_pures.
iDestruct "rest" as "[[fail_vsk fail_psk]|succ]".
  iPoseProof (pterm_session_key_of' with "k_ctx fail_psk") as ">fail".
  wp_bind (send _); iApply wp_send.
  iModIntro.
  iApply pterm_TEncIS; eauto.
  - by rewrite sterm_TKey.
  - iIntros "!> %sp %e_sh".
    by case: (e_hello _ e_sh) => [] -> [] -> [] -> [] _ [] e_enc ->.
  - by iApply pterm_sterm.
  wp_pures; wp_bind (SShare.I.snonce _); iApply SShare.wp_snonce.
  wp_pures; wp_bind (SShare.I.cnonce _); iApply SShare.wp_cnonce.
  wp_pures.
  iApply ("post" $! (Some (_, _, _, _))).
  rewrite e psk_meth_of.
  by iExists _; do 5!iSplit => //; eauto.
wp_bind (send _); iApply wp_send.
  iModIntro.
  iApply pterm_TEncIS; eauto; first by rewrite sterm_TKey.
  - iIntros "!> %sp %e_sp".
    by case: (e_hello _ e_sp) => -> [] -> [] -> [] _ [] _ ->.
  - by iApply pterm_sterm.
iDestruct "succ" as (sp) "(-> & wf & succ)".
wp_pures; wp_bind (SShare.I.snonce _); iApply SShare.wp_snonce.
wp_pures; wp_bind (SShare.I.cnonce _); iApply SShare.wp_cnonce.
wp_pures.
iApply ("post" $! (Some (_, _, _, _))) => //.
iExists _; do 5!iSplit => //.
case: (e_hello _ eq_refl) => ? [] ? [] e_sk [] ? [] ? ?.
iModIntro; iRight; iSplit => //.
iIntros (kt); rewrite -e_sk e.
iModIntro.
iApply blah => //.
Qed.

Definition server N : val := λ: "psk" "g" "verif_key" "other",
  let: "ch" := recv #() in
  bind: "ke" := CParams.I.check N "psk" "g" "other" "ch" in
  let: "ke'" := SShare.I.new "ke" in
  let: "sp"  := term_of_list ["ke'"; "verif_key"; "other"] in
  let: "sh"  := SParams.I.hello N "psk" "sp" in
  send "sh" ;;
  SOME (SShare.I.session_key_of N "psk" "ke'").

Lemma wp_server N psk g verif_key other E Φ :
  pterm psk -∗
  pterm g -∗
  pterm (TKey Enc verif_key) -∗
  pterm (TKey Dec verif_key) -∗
  pterm other -∗
  (∀ sk, opterm sk → Φ (repr sk)) -∗
  WP server N psk g verif_key other @ E {{ Φ }}.
Proof.
iIntros "#p_psk #p_g #p_sign #p_verif #p_other post".
rewrite /server; wp_pures.
wp_bind (recv _); iApply wp_recv.
iIntros (ch) "#p_ch"; wp_pures.
wp_bind (CParams.I.check _ _ _ _ _).
iApply CParams.wp_check.
case e: CParams.check => [ke|] //=; wp_pures; last first.
  by iApply ("post" $! None).
wp_bind (SShare.I.new _); iApply SShare.wp_new; eauto.
- admit.
- by iApply (pterm_sterm with "p_g").
- admit.
iIntros (ke') "%e' #p_ke' token"; wp_pures.
wp_list; wp_term_of_list.
pose sp := SParams.Params ke' verif_key other.
wp_pures.
wp_bind (SParams.I.hello _ _ _); iApply (SParams.wp_hello _ _ sp).
wp_pures; wp_bind (send _); iApply wp_send.
  admit.
wp_pures.
wp_bind (SShare.I.session_key_of _ _ _); iApply SShare.wp_session_key_of.
wp_pures; iApply ("post" $! (Some (SShare.session_key_of N psk ke'))) => /=.
admit. (* Shouldn't be provable: the session key is not public! *)
Admitted.

End Protocol.
