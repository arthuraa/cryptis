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

Section Invariants.

Context `{!heapG Σ, cryptoG Σ}.
Notation iProp := (iProp Σ).

Implicit Types t : term.
Implicit Types Φ : val → iProp.

Definition ctx N : iProp :=
  hash_pred (N.@"psk") (λ _, True)%I ∧
  key_pred (N.@"psk_key") (λ _ _, False)%I ∧
  key_pred (N.@"dh_key") (λ _ _, False)%I.

Global Instance Persistent_ctx N : Persistent (ctx N).
Proof. apply _. Qed.

Program Definition session_info (s : inG Σ sessionR) : sessionG Σ := {|
  session_inG := s;
  fresh_key N t := term_meta_token t (↑N);
  used_key N t := term_meta t N ();
|}.

Next Obligation.
by iIntros (s N t); iApply term_meta_meta_token.
Qed.

Next Obligation.
by iIntros (???); iApply term_meta_set.
Qed.

End Invariants.

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
  ctx N -∗
  wf ke -∗
  pterm (term_of (encode N ke)).
Proof.
iIntros "#(hash & _ & _) #p_ke"; case: ke => [psk|g|psk g] /=.
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

Definition cnonce ke :=
  match ke with
  | Psk _ cn | Dh _ cn _ | PskDh _ _ cn _ => cn
  end.

(** Check if a share has been produced from some known pre-shared key.  If so,
return the value of [psk] on that share. *)

Definition check N psk g ke :=
  match ke with
  | Psk psk' _ =>
    if decide (psk' = THash (Spec.tag (N.@"psk") psk)) then Some psk else None
  | Dh g' _ _ =>
    if decide (g' = g) then Some Spec.zero else None
  | PskDh psk' g' _ _ =>
    if decide (psk' = THash (Spec.tag (N.@"psk") psk) ∧ g' = g) then
      Some psk
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
    (λ: "psk'" <>,
        if: eq_term "psk'" (hash (tag (N.@"psk") "psk")) then SOME "psk" else NONE)
    (λ: "g'" <> <>,
        if: eq_term "g'" "g" then SOME Spec.zero else NONE)
    (λ: "psk'" "g'" <> <>,
        if: eq_term "psk'" (hash (tag (N.@"psk") "psk")) &&
            eq_term "g'" "g" then SOME "psk" else NONE).

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
  Φ (repr (check N psk g ke)) -∗
  WP I.check N psk g (term_of ke) @ E {{ Φ }}.
Proof.
iIntros "?"; rewrite /I.check; wp_pures.
iApply wp_case.
case: ke => [psk' cn|g' cn gx|psk' g' cn gx] //=; wp_pures => //.
- wp_tag; wp_hash; wp_eq_term e; wp_pures; try by rewrite decide_False.
  by rewrite decide_True //=.
- wp_eq_term e; wp_pures; try by rewrite decide_False.
  by rewrite e decide_True.
- wp_tag; wp_hash; wp_eq_term e; wp_pures; last first.
    rewrite decide_False //; intuition congruence.
  rewrite {}e; wp_eq_term e; wp_pures; last first.
    rewrite decide_False //; intuition congruence.
  by rewrite decide_True //=.
Qed.

(* TODO: Add session information *)

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

Instance Persistent_wf ke : Persistent (wf ke).
Proof. case: ke => *; apply _. Qed.

Lemma wf_encode N ke :
  ctx N -∗
  wf ke -∗
  pterm (term_of (encode N ke)).
Proof.
iIntros "#(hash & _ & _) #wf".
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

(* TODO: Add session information *)
Lemma wp_new ke N E Φ :
  Meth.wf ke -∗
  (∀ ke', ⌜ke = meth_of ke'⌝ -∗
          wf ke' -∗
          term_meta_token (cnonce ke') (↑N.@"fresh") -∗
          Φ (term_of ke')) -∗
  WP I.new ke @ E {{ Φ }}.
Proof.
iIntros "#p_ke post"; rewrite /I.new; wp_pures.
iApply Meth.wp_case; case: ke => [psk|g|psk g]; wp_pures.
- wp_bind (mknonce _); iApply (wp_mknonce _ True%I (λ _, True)%I).
  iIntros (cn) "_ #p_cn _ token"; wp_list; wp_term_of_list.
  wp_tag.
  rewrite (term_meta_token_difference _ (↑N.@"fresh")); try set_solver.
  iDestruct "token" as "[token _]".
  iApply ("post" $! (Psk psk cn) with "[] [] token") => //=.
  do !iSplit => //.
  by iApply "p_cn".
- wp_bind (mkdh _); iApply (wp_mkdh (λ _, True)%I).
  iIntros (a) "_ #p_a _"; wp_list.
  wp_bind (mknonce _); iApply (wp_mknonce _ True%I (λ _, True)%I).
  iIntros (cn) "_ #p_cn _ token"; wp_list; wp_term_of_list.
  wp_tag.
  rewrite (term_meta_token_difference _ (↑N.@"fresh")); try set_solver.
  iDestruct "token" as "[token _]".
  iApply ("post" $! (Dh g cn a)) => //=.
  do !iSplit => //.
  by iApply "p_cn".
- wp_bind (mkdh _); iApply (wp_mkdh (λ _, True)%I).
  iIntros (a) "_ #p_a _"; wp_list.
  wp_bind (mknonce _); iApply (wp_mknonce _ True%I (λ _, True)%I).
  iIntros (cn) "_ #p_cn _ token"; wp_list; wp_term_of_list.
  wp_tag.
  rewrite (term_meta_token_difference _ (↑N.@"fresh")); try set_solver.
  iDestruct "token" as "[token _]".
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

Definition encode ke :=
  match ke with
  | Psk psk cn sn => Psk psk cn sn
  | Dh g cn sn gx y => Dh g cn sn gx (TExp g [y])
  | PskDh psk g cn sn gx y => PskDh psk g cn sn gx (TExp g [y])
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

Definition cshare_of ke :=
  match ke with
  | Psk psk cn sn => CShare.Psk psk cn
  | Dh g cn sn x y => CShare.Dh g cn x
  | PskDh psk g cn sn x y => CShare.PskDh psk g cn x
  end.

Definition snonce ke :=
  match ke with
  | Psk _ _ sn | Dh _ _ sn _ _ | PskDh _ _ _ sn _ _ => sn
  end.

(** Compute the session key given the pre-shared key used by the server and its
key share.  In principle, it would be possible to find out what the pre-shared
key is just from the share, but we supply it as a separate parameter to keep
this code closer to its heap lang implementation, which should not be capable of
inverting a hash. *)

Definition session_key_of N psk ke :=
  match ke with
  | Psk _ cn sn =>
    Spec.tag (N.@"psk_key")
             (Spec.of_list [psk; cn; sn])
  | Dh _ _ _ gx y =>
    Spec.tag (N.@"dh_key") (Spec.texp gx y)
  | PskDh _ _ _ _ gx y =>
    Spec.tag (N.@"dh_key") (Spec.texp gx y)
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
      let skey := Spec.tag (N.@"psk_key") (Spec.of_list [psk; cn; sn]) in
      Some [cn; sn; skey]
    else None
  | CShare.Dh g cn x =>
    s_kex ← Spec.untag (nroot.@"dh") ke;
    s_kex ← Spec.to_list s_kex;
    '(g', cn', sn, gx, gy) ← prod_of_list 5 s_kex;
    if decide (g' = g ∧ cn' = cn ∧ gx = TExp g [x]) then
      let skey := Spec.tag (N.@"dh_key") (Spec.texp gy x) in
      Some [cn; sn; skey]
    else None
  | CShare.PskDh psk g cn x =>
    s_kex ← Spec.untag (nroot.@"pskdh") ke;
    s_kex ← Spec.to_list s_kex;
    '(psk', g', cn', sn, gx, gy) ← prod_of_list 6 s_kex;
    if decide (psk' = THash (Spec.tag (N.@"psk") psk)
               ∧ g' = g ∧ cn' = cn ∧ gx = TExp g [x]) then
      let skey := Spec.tag (N.@"dh_key") (Spec.texp gy x) in
      Some [cn; sn; skey]
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

Definition encode : val := λ: "ke",
  case "ke"
    (λ: "psk" "cn" "sn",
      tag (nroot.@"psk") (term_of_list ["psk"; "cn"; "sn"]))
    (λ: "g" "cn" "sn" "gx" "y",
      let: "gy" := texp (tgroup "g") "y" in
      tag (nroot.@"dh") (term_of_list ["g"; "cn"; "sn"; "gx"; "gy"]))
    (λ: "psk" "g" "cn" "sn" "gx" "y",
      let: "gy" := texp (tgroup "g") "y" in
      tag (nroot.@"pskdh") (term_of_list ["psk"; "g"; "cn"; "sn"; "gx"; "gy"])).

Definition session_key_of N : val := λ: "psk" "ke",
  case "ke"
    (λ: <> "c_nonce" "s_nonce",
       tag (N.@"psk_key") (term_of_list ["psk"; "c_nonce"; "s_nonce"]))
    (λ: <> <> <> "gx" "y", tag (N.@"dh_key") (texp "gx" "y"))
    (λ: <> <> <> <> "gx" "y", tag (N.@"dh_key") (texp "gx" "y")).

Definition check N : val := λ: "c_kex" "s_kex",
  CShare.I.case "c_kex"
    (λ: "psk" "c_nonce",
      bind: "s_kex" := untag (nroot.@"psk") "s_kex" in
      bind: "s_kex" := list_of_term "s_kex" in
      list_match: ["psk'"; "c_nonce'"; "s_nonce"] := "s_kex" in
      if: eq_term "psk'" (hash (tag (N.@"psk") "psk"))
          && eq_term "c_nonce'" "c_nonce" then
        let: "skey" :=
           tag (N.@"psk_key") (term_of_list ["psk"; "c_nonce"; "s_nonce"]) in
        SOME ["c_nonce"; "s_nonce"; "skey"]
      else NONE)
    (λ: "g" "cn" "x",
      bind: "s_kex" := untag (nroot.@"dh") "s_kex" in
      bind: "s_kex" := list_of_term "s_kex" in
      list_match: ["g'"; "cn'"; "sn"; "gx"; "gy"] := "s_kex" in
      if: eq_term "g'" "g" && eq_term "cn'" "cn" &&
          eq_term "gx" (texp (tgroup "g") "x") then
        let: "skey" := tag (N.@"dh_key") (texp "gy" "x") in
        SOME ["cn"; "sn"; "skey"]
      else NONE)
    (λ: "psk" "g" "cn" "x",
      bind: "s_kex" := untag (nroot.@"pskdh") "s_kex" in
      bind: "s_kex" := list_of_term "s_kex" in
      list_match: ["psk'"; "g'"; "cn'"; "sn"; "gx"; "gy"] := "s_kex" in
      if: eq_term "psk'" (hash (tag (N.@"psk") "psk")) &&
          eq_term "g'" "g" && eq_term "cn'" "cn" &&
          eq_term "gx" (texp (tgroup "g") "x") then
        let: "skey" := tag (N.@"dh_key") (texp "gy" "x") in
        SOME ["cn"; "sn"; "skey"]
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

Lemma wp_encode ke E Φ :
  Φ (term_of (encode ke)) -∗
  WP I.encode (term_of ke) @ E {{ Φ }}.
Proof.
iIntros "post"; rewrite /I.encode; wp_pures.
iApply wp_case.
case: ke => [psk c_nonce s_nonce|g cn sn gx y|psk g cn sn gx y] /=; wp_pures.
- by wp_list; wp_term_of_list; wp_tag.
- wp_bind (tgroup _); iApply wp_tgroup.
  wp_bind (texp _ _); iApply wp_texp; wp_pures.
  rewrite Spec.texpA.
  wp_list; wp_term_of_list.
  by iApply wp_tag.
- wp_bind (tgroup _); iApply wp_tgroup.
  wp_bind (texp _ _); iApply wp_texp; wp_pures.
  rewrite Spec.texpA.
  wp_list; wp_term_of_list.
  by iApply wp_tag.
Qed.

Lemma wp_session_key_of N psk ke E Φ :
  Φ (session_key_of N psk ke) -∗
  WP I.session_key_of N psk (term_of ke) @ E {{ Φ }}.
Proof.
iIntros "?"; rewrite /I.session_key_of; wp_pures.
iApply wp_case.
case: ke => [???|?????|??????]; wp_pures.
- by wp_list; wp_term_of_list; wp_tag.
- by wp_bind (texp _ _); iApply wp_texp; wp_tag.
- by wp_bind (texp _ _); iApply wp_texp; wp_tag.
Qed.

Lemma wp_check N c_kex s_kex E Φ :
  Φ (repr (check N c_kex s_kex)) -∗
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
  wp_pures; wp_bind (texp _ _); iApply wp_texp; wp_pures.
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
  wp_pures; wp_bind (texp _ _); iApply wp_texp; wp_pures.
  wp_tag; wp_pures.
  by wp_list; wp_pures.
Qed.

Definition wf psk N ke : iProp :=
  match ke with
  | Psk psk' c_nonce s_nonce =>
    ⌜psk' = THash (Spec.tag (N.@"psk") psk)⌝ ∧
    sterm psk ∧ pterm c_nonce ∧ pterm s_nonce
  | Dh g cn sn gx y =>
    pterm g ∧ pterm cn ∧ pterm sn ∧ pterm gx ∧
    dh_seed (λ _, True)%I y
  | PskDh psk' g cn sn gx y =>
    ⌜psk' = THash (Spec.tag (N.@"psk") psk)⌝ ∧
    sterm psk ∧
    pterm g ∧ pterm cn ∧ pterm sn ∧
    pterm gx ∧
    dh_seed (λ _, True)%I y
  end.

Instance Persistent_wf psk N ke : Persistent (wf psk N ke).
Proof. case: ke => *; apply _. Qed.

(* TODO: strengthen *)
Lemma wp_new N psk g k (ke : CShare.t) E Φ :
  CShare.check N psk g ke = Some k →
  sterm psk -∗
  pterm ke -∗
  (∀ ke',
      ⌜ke = cshare_of ke'⌝ -∗
      wf psk N ke' -∗
      term_meta_token (snonce ke') (↑N.@"fresh") -∗
      Φ (term_of ke')) -∗
  WP I.new ke @ E {{ Φ }}.
Proof.
iIntros (e_check) "#s_psk #p_ke post"; rewrite /I.new; wp_pures.
iApply CShare.wp_case.
case: ke => [psk' c_nonce|g' cn gx|psk' g' cn gx] /= in e_check *; wp_pures.
- case: decide => [->|//] in e_check *.
  wp_bind (mknonce _); iApply (wp_mknonce _ True%I (λ _, True)%I).
  iIntros (a) "_ #pred_a _ token"; wp_list; wp_term_of_list.
  wp_tag; wp_pures.
  rewrite (term_meta_token_difference _ (↑N.@"fresh")); try set_solver.
  iDestruct "token" as "[token _]".
  iApply ("post" $! (Psk (THash _) c_nonce a)) => //=.
  iSplit => //.
  rewrite !pterm_tag !pterm_of_list /=.
  iDestruct "p_ke" as "(? & ? & _)".
  do !iSplit => //.
  by iApply "pred_a".
- case: decide => [->|//] in e_check *.
  wp_bind (mkdh _); iApply (wp_mkdh (λ _, True)%I).
  iIntros (a) "_ #pred_a _"; wp_list.
  wp_bind (mknonce _); iApply (wp_mknonce _ True%I (λ _, True)%I).
  iIntros (sn) "_ #p_sn _ token"; wp_list; wp_term_of_list.
  rewrite (term_meta_token_difference _ (↑N.@"fresh")); try set_solver.
  iDestruct "token" as "[token _]".
  wp_tag; wp_pures.
  iApply ("post" $! (Dh g cn sn gx a)) => //=.
  rewrite !pterm_tag !pterm_of_list /=.
  iDestruct "p_ke" as "(? & ? & ? & _)".
  do !iSplit => //.
  by iApply "p_sn".
- case: decide => [[-> ->]|//] in e_check *.
  wp_bind (mkdh _); iApply (wp_mkdh (λ _, True)%I).
  iIntros (a) "_ #pred_a _"; wp_list.
  wp_bind (mknonce _); iApply (wp_mknonce _ True%I (λ _, True)%I).
  iIntros (sn) "_ #p_sn _ token"; wp_list; wp_term_of_list.
  rewrite (term_meta_token_difference _ (↑N.@"fresh")); try set_solver.
  iDestruct "token" as "[token _]".
  wp_tag; wp_pures.
  iApply ("post" $! (PskDh _ g cn sn gx a)) => //.
  rewrite !pterm_tag !pterm_of_list /=.
  iDestruct "p_ke" as "(? & ? & ? & ? & _)".
  do !iSplit => //.
  by iApply "p_sn".
Qed.

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

Definition check N psk g other ch :=
  ch ← Spec.to_list ch;
  '(ch, mac) ← prod_of_list 2 ch;
  ch' ← Spec.to_list ch;
  '(ke, other') ← prod_of_list 2 ch';
  ke ← CShare.of_term ke;
  psk ← CShare.check N psk g ke;
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
  bind: "psk" := CShare.I.check N "psk" "g" "ke" in
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
case: CShare.check => [psk'|] /=; wp_pures => //.
wp_list; wp_term_of_list; wp_tag; wp_hash.
wp_eq_term e'; wp_pures; last first.
  rewrite decide_False //; intuition congruence.
rewrite {}e' {other'}.
wp_eq_term e'; wp_pures; last first.
  rewrite decide_False //; intuition congruence.
by rewrite {}e' decide_True //.
Qed.

End Proofs.

End CParams.

Coercion CParams.term_of : CParams.t >-> term.

Module SParams.

Record t := Params {
  share : SShare.t;
  verif_key : term;
  other : term;
}.

Definition encode sp :=
  {| share := SShare.encode (share sp);
     verif_key := verif_key sp;
     other := other sp |}.

Definition term_of sp :=
  Spec.of_list [
    SShare.term_of (share sp);
    verif_key sp;
    other sp
  ].

Definition hello_pub sp :=
  Spec.of_list [
    SShare.term_of (SShare.encode (share sp));
    other sp
  ].

Definition hello N psk sp :=
  let pub := hello_pub sp in
  let enc := Spec.of_list [
    TKey Dec (verif_key sp);
    TEnc (verif_key sp) (Spec.tag (N.@"server_hello_sig") (THash pub))
  ] in let session_key := SShare.session_key_of N psk (share sp) in
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
  '(_, _, session_key) ← prod_of_list 3 res;
  dec_sig ← Spec.tdec (N.@"server_hello") (TKey Dec session_key) sig;
  dec_sig ← Spec.to_list dec_sig;
  '(verif_key, sig) ← prod_of_list 2 dec_sig;
  if decide (other' = CParams.other cp) then
    if verify (N.@"server_hello_sig") verif_key pub sig then
      Some res
    else None
  else None.

Module I.

Definition case : val := λ: "sp" "f",
  bind: "sp'" := list_of_term "sp" in
  list_match: ["kex"; "verif_key"; "other"] := "sp'" in
  "f" "kex" "verif_key" "other".

Definition hello_pub : val := λ: "sp",
  case "sp" (λ: "kex" "verif_key" "other",
    term_of_list [SShare.I.encode "kex"; "other"]).

Definition hello N : val := λ: "psk" "sp",
  case "sp" (λ: "kex" "verif_key" "other",
    let: "pub" := hello_pub "sp" in
    let: "verif_key" := mkkey "verif_key" in
    bind: "enc" :=
      tenc (N.@"server_hello_sig") (Fst "verif_key") (hash "pub") in
    let: "enc" := term_of_list [Snd "verif_key"; "enc"] in
    let: "session_key" := mkkey (SShare.I.session_key_of N "psk" "kex") in
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
  list_match: ["cn"; "sn"; "session_key"] := "res" in
  let: "sk" := mkkey "session_key" in
  bind: "dec_sig" := tdec (N.@"server_hello") (Snd "sk") "sig" in
  bind: "dec_sig" := list_of_term "dec_sig" in
  list_match: ["verif_key"; "sig"] := "dec_sig" in
  if: eq_term "s_other" "c_other" then
    if: verify (N.@"server_hello_sig") "verif_key" "pub" "sig" then
      SOME "res"
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

Lemma wp_hello_pub sp E Φ :
  Φ (hello_pub sp) -∗
  WP I.hello_pub (term_of sp) @ E {{ Φ }}.
Proof.
iIntros "?"; rewrite /I.hello_pub; wp_pures.
iApply wp_case; wp_pures.
wp_list.
wp_bind (SShare.I.encode _); iApply SShare.wp_encode.
by wp_list; wp_term_of_list.
Qed.

Lemma wp_hello N psk sp E Φ :
  Φ (hello N psk sp) -∗
  WP I.hello N psk (term_of sp) @ E {{ Φ }}.
Proof.
iIntros "?"; rewrite /I.hello; wp_pures.
iApply wp_case; wp_pures.
wp_bind (I.hello_pub _); iApply wp_hello_pub; wp_pures.
wp_bind (mkkey _); iApply wp_mkkey; wp_pures.
wp_hash; wp_tenc; wp_pures.
wp_list; wp_term_of_list; wp_pures.
wp_bind (SShare.I.session_key_of _ _ _); iApply SShare.wp_session_key_of.
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
  Φ (repr (check N cp sh)) -∗
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
wp_list_match => [cn sn session_key -> {res}|ne]; wp_finish; last first.
  by rewrite prod_of_list_neq.
rewrite [in prod_of_list _ _]unlock /=.
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

End Proofs.

End SParams.

Coercion SParams.term_of : SParams.t >-> term.

Section Protocol.

Context `{!heapG Σ, !cryptoG Σ, !network Σ, !inG Σ sessionR}.
Notation iProp := (iProp Σ).

Implicit Types t : term.
Implicit Types s : session_view.
Implicit Types rl : role.
Implicit Types Φ : val → iProp.

Definition client N : val := λ: "kex" "other",
  let: "kex" := CShare.I.new "kex" in
  let: "cp"  := term_of_list ["kex"; "other"] in
  let: "ch"  := CParams.I.hello N "cp" in
  send "ch";;
  let: "sh" := recv #() in
  SParams.I.check N "cp" "sh".

Existing Instance session_info.

Definition inv rl (kA kB nA nB : term) : iProp :=
  match rl with
  | Init => True%I
  | Resp => True%I
  end.

Lemma wp_client γ N ke other E Φ :
  ctx N -∗
  session_ctx γ N inv -∗
  Meth.wf ke -∗
  pterm other -∗
  (∀ cp sh,
      ⌜ke = CShare.meth_of (CParams.share cp)⌝ →
      ⌜other = CParams.other cp⌝ →
      pterm sh →
      Φ (repr (SParams.check N cp sh))) -∗
  WP client N ke other @ E {{ Φ }}.
Proof.
iIntros "#ctx #sess #p_ke #p_other post".
rewrite /client; wp_pures.
wp_bind (CShare.I.new _); iApply (CShare.wp_new _ N) => //.
iIntros (ke' e) "#p_ke' token"; wp_pures.
wp_list; wp_term_of_list.
wp_pures; wp_bind (CParams.I.hello _ _).
pose cp := {| CParams.share := ke'; CParams.other := other |}.
iApply (CParams.wp_hello N cp).
wp_pures; wp_bind (send _); iApply wp_send.
  admit.
wp_pures; wp_bind (recv _); iApply wp_recv.
iIntros (sh) "p_sh"; wp_pures.
iApply (SParams.wp_check N cp).
by iApply "post" => //.
Admitted.

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
