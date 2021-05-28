(*

Transcribed from https://github.com/Inria-Prosecco/reftls

*)


From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl namespace_map frac.
From iris.base_logic.lib Require Import auth.
From iris.heap_lang Require Import notation proofmode.
From crypto Require Import lib guarded term crypto primitives tactics session.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

Definition ctx := crypto_enc N inv.

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

Fixpoint prod_of_list_aux_type A B n :=
  match n with
  | 0 => A
  | S n => prod_of_list_aux_type (A * B)%type B n
  end.

Fixpoint prod_of_list_aux {A B} n :
  A → list B → option (prod_of_list_aux_type A B n) :=
  match n with
  | 0 => fun x ys =>
    match ys with
    | [] => Some x
    | _  => None
    end
  | S n => fun x ys =>
    match ys with
    | [] => None
    | y :: ys => prod_of_list_aux n (x, y) ys
    end
  end.

Definition prod_of_list_type A n : Type :=
  match n with
  | 0 => unit
  | S n => prod_of_list_aux_type A A n
  end.

Fact prod_of_list_key : unit. Proof. exact: tt. Qed.

Definition prod_of_list : ∀ {A} n, list A → option (prod_of_list_type A n) :=
  locked_with prod_of_list_key (
    λ A n, match n return list A → option (prod_of_list_type A n) with
           | 0 => fun xs => match xs with
                            | [] => Some tt
                            | _  => None
                            end
           | S n => fun xs => match xs with
                              | [] => None
                              | x :: xs => prod_of_list_aux n x xs
                              end
           end).

Canonical prod_of_list_unlockable :=
  [unlockable of @prod_of_list].

Lemma prod_of_list_neq {A} n (xs : list A) :
  length xs ≠ n → prod_of_list n xs = None.
Proof.
rewrite unlock; case: n xs=> [|n] [|x xs] //= ne.
have {}ne : length xs ≠ n by congruence.
suffices : ∀ B (x : B), prod_of_list_aux n x xs = None by apply.
elim: n xs {x} => [|n IH] [|y ys] //= in ne * => B x.
rewrite IH //; congruence.
Qed.

Definition tlsN := nroot.@"tls".

Module S.

Definition zero : term := TInt 0.

Definition thash (l : string) ts :=
  THash (Spec.tag (nroot.@l) (Spec.of_list ts)).

Variant key_exch_prop :=
| PskP of term & term
| DhP of term & term
| PskDhP of term & term & term.

Definition ser_key_exch_prop ke :=
  match ke with
  | PskP psk nonce => PskP (THash psk) nonce
  | DhP g x => DhP g (Spec.texp g x)
  | PskDhP psk g x => PskDhP (THash psk) g (Spec.texp g x)
  end.

Definition psk_of_key_exch_prop ke :=
  match ke with
  | PskP psk _ => psk
  | DhP _ _ => zero
  | PskDhP psk _ _ => psk
  end.

Record client_params := ClientParams {
  cp_key_exch : key_exch_prop;
  cp_other : term;
}.

Definition ser_client_params cp :=
  {| cp_key_exch := ser_key_exch_prop (cp_key_exch cp);
     cp_other    := cp_other cp; |}.

Variant key_exch :=
| Psk of term & term & term
| Dh of term & term & term
| PskDh of term & term & term & term.

Definition ser_key_exch ke :=
  match ke with
  | Psk psk c_nonce s_nonce => Psk (THash psk) c_nonce s_nonce
  | Dh g gx y => Dh g gx (Spec.texp g y)
  | PskDh psk g gx y => PskDh (THash psk) g gx (Spec.texp g y)
  end.

Definition psk_of_key_exch ke :=
  match ke with
  | Psk psk _ _ => psk
  | Dh _ _ _ => zero
  | PskDh psk _ _ _ => psk
  end.

Definition client_share ke :=
  match ke with
  | Psk psk c_nonce s_nonce => PskP psk c_nonce
  | Dh g x y => DhP g x
  | PskDh psk g x y => PskDhP psk g x
  end.

Record server_params := ServerParams {
  sp_key_exch : key_exch;
  sp_verif_key : term;
  sp_other : term;
}.

Definition ser_server_params sp :=
  {| sp_key_exch := ser_key_exch (sp_key_exch sp);
     sp_verif_key := sp_verif_key sp;
     sp_other := sp_other sp |}.

Definition client_params_of_server sp :=
  {| cp_key_exch := client_share (sp_key_exch sp);
     cp_other := sp_other sp; |}.

Definition term_of_key_exch_prop ke :=
  match ke with
  | PskP psk c_nonce => Spec.tag (nroot.@"psk") (Spec.of_list [psk; c_nonce])
  | DhP g x => Spec.tag (nroot.@"dh") (Spec.of_list [g; x])
  | PskDhP psk g x => Spec.tag (nroot.@"pskdh") (Spec.of_list [psk; g; x])
  end.

Definition term_of_key_exch ke :=
  match ke with
  | Psk psk c_nonce s_nonce =>
    Spec.tag (nroot.@"psk") (Spec.of_list [psk; c_nonce; s_nonce])
  | Dh g x y => Spec.tag (nroot.@"dh") (Spec.of_list [g; x; y])
  | PskDh psk g x y => Spec.tag (nroot.@"pskdh") (Spec.of_list [psk; g; x; y])
  end.

Definition term_of_client_params cp :=
  Spec.of_list [
    term_of_key_exch_prop (cp_key_exch cp);
    cp_other cp
  ].

Definition term_of_server_params sp :=
  Spec.of_list [
    term_of_key_exch (sp_key_exch sp);
    sp_verif_key sp;
    sp_other sp
  ].

Definition client_hello cp :=
  let ch := term_of_client_params (ser_client_params cp) in
  let psk := psk_of_key_exch_prop (cp_key_exch cp) in
  let mac := thash "binder" [psk; ch] in
  Spec.of_list [ch; mac].

Definition server_hello_pub sp :=
  Spec.of_list [
    term_of_key_exch (ser_key_exch (sp_key_exch sp));
    sp_other sp
  ].

Definition session_key_of_key_exch ke :=
  match ke with
  | Psk psk c_nonce s_nonce => Spec.of_list [psk; c_nonce; s_nonce]
  | Dh _ gx y => Spec.texp gx y
  | PskDh _ _ gx y => Spec.texp gx y
  end.

Definition server_hello sp :=
  let pub := server_hello_pub sp in
  let enc := Spec.of_list [
    TKey Dec (sp_verif_key sp);
    TEnc (sp_verif_key sp) (Spec.tag (tlsN.@"server_hello_sig") (THash pub))
  ] in let session_key := session_key_of_key_exch (sp_key_exch sp) in
  Spec.of_list [
    pub;
    TEnc session_key (Spec.tag (tlsN.@"server_hello") enc)
  ].

Definition check_session_key c_kex s_kex :=
  match c_kex with
  | PskP psk c_nonce =>
    s_kex ← Spec.untag (nroot.@"psk") s_kex;
    s_kex ← Spec.to_list s_kex;
    '(psk', c_nonce', s_nonce) ← prod_of_list 3 s_kex;
    if decide (psk' = THash psk ∧ c_nonce' = c_nonce) then
      Some (Spec.of_list [psk; c_nonce; s_nonce])
    else None
  | DhP g x =>
    s_kex ← Spec.untag (nroot.@"dh") s_kex;
    s_kex ← Spec.to_list s_kex;
    '(g', gx, gy) ← prod_of_list 3 s_kex;
    if decide (g' = g ∧ gx = Spec.texp g x) then Some (Spec.texp gy x)
    else None
  | PskDhP psk g x =>
    s_kex ← Spec.untag (nroot.@"pskdh") s_kex;
    s_kex ← Spec.to_list s_kex;
    '(psk', g', gx, gy) ← prod_of_list 4 s_kex;
    if decide (psk' = THash psk ∧ g' = g ∧ gx = Spec.texp g x) then
      Some (Spec.texp gy x)
    else None
  end.

Definition verify N k x sig :=
  match Spec.tdec N k sig with
  | Some y => bool_decide (y = THash x)
  | None => false
  end.

Definition check_server_hello cp sp : bool :=
  let res :=
      sp ← Spec.to_list sp;
      '(pub, sig) ← prod_of_list 2 sp;
      pub' ← Spec.to_list pub;
      '(kex, other) ← prod_of_list 2 pub';
      session_key ← check_session_key (cp_key_exch cp) kex;
      dec_sig ← Spec.tdec (tlsN.@"server_hello") session_key sig;
      dec_sig ← Spec.to_list dec_sig;
      '(verif_key, sig) ← prod_of_list 2 dec_sig;
      if decide (other = cp_other cp) then
        Some (verify (tlsN.@"server_hello_sig") verif_key pub sig)
      else None in
  if res is Some res then res else false.

End S.

Module I.

Section I.

Context `{!heapG Σ, !cryptoG Σ, !network Σ}.
Notation iProp := (iProp Σ).

Implicit Types t : term.
Implicit Types s : session_view.
Implicit Types rl : role.
Implicit Types Φ : val → iProp.

Definition key_exch_prop_match : val := λ: "ke" "f_psk" "f_dh" "f_pskdh",
  match: untag (nroot.@"psk") "ke" with
    SOME "args" =>
    bind: "l" := list_of_term "args" in
    list_match: ["psk"; "c_nonce"] := "l" in
    "f_psk" "psk" "c_nonce"
  | NONE =>
  match: untag (nroot.@"dh") "ke" with
    SOME "args" =>
    bind: "l" := list_of_term "args" in
    list_match: ["g"; "x"] := "l" in
    "f_dh" "g" "x"
  | NONE =>
  match: untag (nroot.@"pskdh") "ke" with
    SOME "args" =>
    bind: "l" := list_of_term "args" in
    list_match: ["psk"; "g"; "x"] := "l" in
    "f_pskdh" "psk" "g" "x"
  | NONE => NONE end end end.

Lemma wp_key_exch_prop_match ke (f_psk f_dh f_pskdh : val) E Φ :
  match ke with
  | S.PskP psk c_nonce => WP f_psk psk c_nonce @ E {{ Φ }}
  | S.DhP g x => WP f_dh g x @ E {{ Φ }}
  | S.PskDhP psk g x => WP f_pskdh psk g x @ E {{ Φ }}
  end -∗
  WP key_exch_prop_match (S.term_of_key_exch_prop ke) f_psk f_dh f_pskdh
     @ E {{ Φ }}.
Proof.
iIntros "post"; rewrite /key_exch_prop_match.
wp_untag_eq psk e_psk.
  case: ke e_psk => [??|??|???] /= /Spec.tag_inj []; try set_solver.
  move=> _ <-; wp_pures; do !rewrite subst_list_match /=.
  wp_list_of_term_eq l e_l; last by rewrite Spec.of_listK in e_l.
  move/Spec.of_list_inj: e_l => {l} <-.
  by wp_list_match => // _ _ [<- <-].
wp_untag_eq args e_dh.
  case: ke e_psk e_dh => [??|g x|???] /= e_psk /Spec.tag_inj []; try set_solver.
  move=> _ <- {e_psk args}; wp_pures; do !rewrite subst_list_match /=.
  wp_list_of_term_eq l e_l; last by rewrite Spec.of_listK in e_l.
  move/Spec.of_list_inj: e_l => {l} <-.
  by wp_list_match => // _ _ [<- <-].
wp_untag_eq args e_pskdh; last first.
  by case: ke e_psk e_dh e_pskdh =>> /=; rewrite Spec.tagK.
case: ke e_psk e_dh e_pskdh
  => [??|??|psk g x] /= e_psk e_dh /Spec.tag_inj []; try set_solver.
move=> _ <- {e_psk e_dh args}; wp_pures; do !rewrite subst_list_match /=.
wp_list_of_term_eq l e_l; last by rewrite Spec.of_listK in e_l.
move/Spec.of_list_inj: e_l => {l} <-.
by wp_list_match => // _ _ _ [<- <- <-].
Qed.

Definition key_exch_match : val := λ: "ke" "f_psk" "f_dh" "f_pskdh",
  match: untag (nroot.@"psk") "ke" with
    SOME "args" =>
    bind: "l" := list_of_term "args" in
    list_match: ["psk"; "c_nonce"; "s_nonce"] := "l" in
    "f_psk" "psk" "c_nonce" "s_nonce"
  | NONE =>
  match: untag (nroot.@"dh") "ke" with
    SOME "args" =>
    bind: "l" := list_of_term "args" in
    list_match: ["g"; "x"; "y"] := "l" in
    "f_dh" "g" "x" "y"
  | NONE =>
  match: untag (nroot.@"pskdh") "ke" with
    SOME "args" =>
    bind: "l" := list_of_term "args" in
    list_match: ["psk"; "g"; "x"; "y"] := "l" in
    "f_pskdh" "psk" "g" "x" "y"
  | NONE => NONE end end end.

Lemma wp_key_exch_match ke (f_psk f_dh f_pskdh : val) E Φ :
  match ke with
  | S.Psk psk c_nonce s_nonce => WP f_psk psk c_nonce s_nonce @ E {{ Φ }}
  | S.Dh g x y => WP f_dh g x y @ E {{ Φ }}
  | S.PskDh psk g x y => WP f_pskdh psk g x y @ E {{ Φ }}
  end -∗
  WP key_exch_match (S.term_of_key_exch ke) f_psk f_dh f_pskdh
     @ E {{ Φ }}.
Proof.
iIntros "post"; rewrite /key_exch_match.
wp_untag_eq psk e_psk.
  case: ke e_psk => [???|???|????] /= /Spec.tag_inj []; try set_solver.
  move=> _ <-; wp_pures; do !rewrite subst_list_match /=.
  wp_list_of_term_eq l e_l; last by rewrite Spec.of_listK in e_l.
  move/Spec.of_list_inj: e_l => {l} <-.
  by wp_list_match => // _ _ _ [<- <- <-].
wp_untag_eq args e_dh.
  case: ke e_psk e_dh => [???|g x y|????] /= e_psk /Spec.tag_inj []; try set_solver.
  move=> _ <- {e_psk args}; wp_pures; do !rewrite subst_list_match /=.
  wp_list_of_term_eq l e_l; last by rewrite Spec.of_listK in e_l.
  move/Spec.of_list_inj: e_l => {l} <-.
  by wp_list_match => // _ _ _ [<- <- <-].
wp_untag_eq args e_pskdh; last first.
  by case: ke e_psk e_dh e_pskdh =>> /=; rewrite Spec.tagK.
case: ke e_psk e_dh e_pskdh
  => [???|???|psk g x y] /= e_psk e_dh /Spec.tag_inj []; try set_solver.
move=> _ <- {e_psk e_dh args}; wp_pures; do !rewrite subst_list_match /=.
wp_list_of_term_eq l e_l; last by rewrite Spec.of_listK in e_l.
move/Spec.of_list_inj: e_l => {l} <-.
by wp_list_match => // _ _ _ _ [<- <- <- <-].
Qed.

Definition ser_key_exch_prop : val := λ: "ke",
  key_exch_prop_match "ke"
    (λ: "psk" "c_nonce",
      tag (nroot.@"psk") (term_of_list [hash "psk"; "c_nonce"]))
    (λ: "g" "x",
      let: "gx" := texp "g" "x" in
      tag (nroot.@"dh") (term_of_list ["g"; "gx"]))
    (λ: "psk" "g" "x",
      let: "gx" := texp "g" "x" in
      tag (nroot.@"pskdh") (term_of_list [hash "psk"; "g"; "gx"])).

Lemma wp_ser_key_exch_prop ke E Φ :
  Φ (S.term_of_key_exch_prop (S.ser_key_exch_prop ke)) -∗
  WP ser_key_exch_prop (S.term_of_key_exch_prop ke) @ E {{ Φ }}.
Proof.
iIntros "post"; rewrite /ser_key_exch_prop; wp_pures.
iApply wp_key_exch_prop_match.
case: ke => [psk c_nonce|g x|psk g x] /=; wp_pures.
- by wp_list; wp_hash; wp_list; wp_term_of_list; wp_tag.
- wp_bind (texp _ _); iApply wp_texp; wp_pures.
  wp_list; wp_term_of_list.
  by iApply wp_tag.
- wp_bind (texp _ _); iApply wp_texp; wp_pures.
  wp_list; wp_hash; wp_list; wp_term_of_list.
  by iApply wp_tag.
Qed.

Definition ser_key_exch : val := λ: "ke",
  key_exch_match "ke"
    (λ: "psk" "c_nonce" "s_nonce",
      tag (nroot.@"psk") (term_of_list [hash "psk"; "c_nonce"; "s_nonce"]))
    (λ: "g" "gx" "y",
      let: "gy" := texp "g" "y" in
      tag (nroot.@"dh") (term_of_list ["g"; "gx"; "gy"]))
    (λ: "psk" "g" "gx" "y",
      let: "gy" := texp "g" "y" in
      tag (nroot.@"pskdh") (term_of_list [hash "psk"; "g"; "gx"; "gy"])).

Lemma wp_ser_key_exch ke E Φ :
  Φ (S.term_of_key_exch (S.ser_key_exch ke)) -∗
  WP ser_key_exch (S.term_of_key_exch ke) @ E {{ Φ }}.
Proof.
iIntros "post"; rewrite /ser_key_exch; wp_pures.
iApply wp_key_exch_match.
case: ke => [psk c_nonce s_nonce|g gx y|psk g gx y] /=; wp_pures.
- by wp_list; wp_hash; wp_list; wp_term_of_list; wp_tag.
- wp_bind (texp _ _); iApply wp_texp; wp_pures.
  wp_list; wp_term_of_list.
  by iApply wp_tag.
- wp_bind (texp _ _); iApply wp_texp; wp_pures.
  wp_list; wp_hash; wp_list; wp_term_of_list.
  by iApply wp_tag.
Qed.

Definition psk_of_key_exch_prop : val := λ: "ke",
  key_exch_prop_match "ke"
    (λ: "psk" <>, "psk")
    (λ: <> <>, S.zero)
    (λ: "psk" <> <>, "psk").

Lemma wp_psk_of_key_exch_prop ke E Φ :
  Φ (S.psk_of_key_exch_prop ke) -∗
  WP psk_of_key_exch_prop (S.term_of_key_exch_prop ke) @ E {{ Φ }}.
Proof.
iIntros "post"; rewrite /psk_of_key_exch_prop; wp_pures.
iApply wp_key_exch_prop_match.
by case: ke => [psk ?|? ?|psk ? ?]; wp_pures.
Qed.

Definition thash (l : string) : val := λ: "ts",
  hash (tag (nroot.@l) (term_of_list "ts")).

Lemma wp_thash l ts E Φ :
  Φ (S.thash l ts) -∗
  WP thash l (repr ts) @ E {{ Φ }}.
Proof.
iIntros "post"; rewrite /thash; wp_pures.
by wp_term_of_list; wp_tag; wp_hash.
Qed.

Definition client_hello : val := λ: "cp",
  bind: "cp" := list_of_term "cp" in
  list_match: ["kex"; "other"] := "cp" in
  let: "ts" := term_of_list [ser_key_exch_prop "kex"; "other"] in
  let: "psk" := psk_of_key_exch_prop "kex" in
  let: "mac" := thash "binder" ["psk"; "ts"] in
  term_of_list ["ts"; "mac"].

Lemma wp_client_hello cp E Φ :
  Φ (S.client_hello cp) -∗
  WP client_hello (S.term_of_client_params cp) @ E {{ Φ }}.
Proof.
iIntros "post"; rewrite /client_hello; wp_pures.
wp_list_of_term_eq t e; last by rewrite Spec.of_listK in e.
move/Spec.of_list_inj: e => <-.
wp_list_match => // _ _ [] <- <-.
wp_list; wp_bind (ser_key_exch_prop _); iApply wp_ser_key_exch_prop.
wp_list; wp_term_of_list; wp_pures.
wp_bind (psk_of_key_exch_prop _); iApply wp_psk_of_key_exch_prop.
wp_pures; wp_list; wp_bind (thash _ _); iApply wp_thash.
by wp_pures; wp_list; iApply wp_term_of_list.
Qed.

Definition psk_of_key_exch : val := λ: "ke",
  key_exch_match "ke"
    (λ: "psk" <> <>, "psk")
    (λ: <> <> <>, S.zero)
    (λ: "psk" <> <> <>, "psk").

Lemma wp_psk_of_key_exch ke E Φ :
  Φ (S.psk_of_key_exch ke) -∗
  WP psk_of_key_exch (S.term_of_key_exch ke) @ E {{ Φ }}.
Proof.
iIntros "post"; rewrite /psk_of_key_exch; wp_pures.
iApply wp_key_exch_match.
by case: ke => [psk ??|???|psk ???]; wp_pures.
Qed.

(*Definition master_secret : val := λ: "ke",
  term_of_list [psk_of_key_exch "ke"; dh_of_key_exch "ke"].

Lemma wp_master_secret ke E Φ :
  Φ (S.master_secret ke) -∗
  WP master_secret (S.term_of_key_exch ke) @ E {{ Φ }}.
Proof.
iIntros "post"; rewrite /master_secret; wp_pures.
wp_bind (dh_of_key_exch _); iApply wp_dh_of_key_exch.
wp_list; wp_bind (psk_of_key_exch _); iApply wp_psk_of_key_exch.
by wp_list; wp_term_of_list.
Qed.

Definition client_key : val := λ: "ke",
  thash "client_key" [master_secret "ke"].

Lemma wp_client_key ke E Φ :
  Φ (S.client_key ke) -∗
  WP client_key (S.term_of_key_exch ke) @ E {{ Φ }}.
Proof.
iIntros "?"; rewrite /client_key; wp_pures.
wp_bind (master_secret _); iApply wp_master_secret.
wp_list; by iApply wp_thash.
Qed.

Definition server_key : val := λ: "ke",
  thash "server_key" [master_secret "ke"].

Lemma wp_server_key ke E Φ :
  Φ (S.server_key ke) -∗
  WP server_key (S.term_of_key_exch ke) @ E {{ Φ }}.
Proof.
iIntros "?"; rewrite /server_key; wp_pures.
wp_bind (master_secret _); iApply wp_master_secret.
wp_list; by iApply wp_thash.
Qed.

Definition client_share : val := λ: "ke",
  key_exch_match "ke"
    (λ: "psk", "ke")
    (λ: "g" "x" "y", tag (nroot.@"dh") (term_of_list ["g"; "x"]))
    (λ: "psk" "g" "x" "y", tag (nroot.@"pskdh") (term_of_list ["psk"; "g"; "x"])).

Lemma wp_client_share ke E Φ :
  Φ (S.term_of_key_exch_prop (S.client_share ke)) -∗
  WP client_share (S.term_of_key_exch ke) @ E {{ Φ }}.
Proof.
iIntros "?"; rewrite /client_share; wp_pures.
iApply wp_key_exch_match.
case: ke => [?|???|????] //=; wp_pures => //.
- by wp_list; wp_term_of_list; iApply wp_tag.
- by wp_list; wp_term_of_list; iApply wp_tag.
Qed.

Definition client_params_of_sess : val := λ: "sp",
  bind: "sp" := list_of_term "sp" in
  list_match: ["version"; "c_nonce"; "s_nonce"; "kex";
               "hash_alg"; "ae_alg"; "verif_key"] := "sp" in
  term_of_list [
    "version";
    "c_nonce";
    client_share "kex";
    "hash_alg";
    "ae_alg"
  ].

Lemma wp_client_params_of_sess sp E Φ :
  Φ (S.term_of_client_params (S.client_params_of_sess sp)) -∗
  WP client_params_of_sess (S.term_of_sess_params sp) @ E {{ Φ }}.
Proof.
iIntros "?"; rewrite /client_params_of_sess; wp_pures.
wp_list_of_term_eq l e; last by rewrite Spec.of_listK in e.
move/Spec.of_list_inj: e => <- {l}.
wp_list_match => // ??????? [] *; subst.
wp_list; wp_bind (client_share _); iApply wp_client_share.
by wp_list; wp_term_of_list.
Qed.
*)

Definition server_params_match : val := λ: "sp" "f",
  bind: "sp'" := list_of_term "sp" in
  list_match: ["kex"; "verif_key"; "other"] := "sp'" in
  "f" "kex" "verif_key" "other".

Lemma wp_server_params_match sp (f : val) E Φ :
  WP f (S.term_of_key_exch (S.sp_key_exch sp))
       (S.sp_verif_key sp)
       (S.sp_other sp) @ E {{ Φ }} -∗
  WP server_params_match (S.term_of_server_params sp) f @ E {{ Φ }}.
Proof.
iIntros "?"; rewrite /server_params_match; wp_pures.
wp_list_of_term_eq l e; last by rewrite Spec.of_listK in e.
move/Spec.of_list_inj: e => {l} <-.
by wp_list_match => // _ _ _ [] <- <- <-.
Qed.

Definition server_hello_pub : val := λ: "sp",
  server_params_match "sp" (λ: "kex" "verif_key" "other",
    term_of_list [ser_key_exch "kex"; "other"]).

Lemma wp_server_hello_pub sp E Φ :
  Φ (S.server_hello_pub sp) -∗
  WP server_hello_pub (S.term_of_server_params sp) @ E {{ Φ }}.
Proof.
iIntros "?"; rewrite /server_hello_pub; wp_pures.
iApply wp_server_params_match; wp_pures.
wp_list.
wp_bind (ser_key_exch _); iApply wp_ser_key_exch.
by wp_list; wp_term_of_list.
Qed.

Definition session_key_of_key_exch : val := λ: "ke",
  key_exch_match "ke"
    (λ: "psk" "c_nonce" "s_nonce",
       term_of_list ["psk"; "c_nonce"; "s_nonce"])
    (λ: <> "gx" "y", texp "gx" "y")
    (λ: <> <> "gx" "y", texp "gx" "y").

Lemma wp_session_key_of_key_exch ke E Φ :
  Φ (S.session_key_of_key_exch ke) -∗
  WP session_key_of_key_exch (S.term_of_key_exch ke) @ E {{ Φ }}.
Proof.
iIntros "?"; rewrite /session_key_of_key_exch; wp_pures.
iApply wp_key_exch_match.
case: ke => [???|???|????]; wp_pures.
- by wp_list; wp_term_of_list.
- by iApply wp_texp.
- by iApply wp_texp.
Qed.

Definition server_hello : val := λ: "sp",
  server_params_match "sp" (λ: "kex" "verif_key" "other",
    let: "pub" := server_hello_pub "sp" in
    let: "verif_key" := mkkey "verif_key" in
    bind: "enc" :=
      tenc (tlsN.@"server_hello_sig") (Fst "verif_key") (hash "pub") in
    let: "enc" := term_of_list [Snd "verif_key"; "enc"] in
    let: "session_key" := mkkey (session_key_of_key_exch "kex") in
    bind: "enc" := tenc (tlsN.@"server_hello") (Fst "session_key") "enc" in
    term_of_list ["pub"; "enc"]
  ).

Lemma wp_server_hello sp E Φ :
  Φ (S.server_hello sp) -∗
  WP server_hello (S.term_of_server_params sp) @ E {{ Φ }}.
Proof.
iIntros "?"; rewrite /server_hello; wp_pures.
iApply wp_server_params_match; wp_pures.
wp_bind (server_hello_pub _); iApply wp_server_hello_pub; wp_pures.
wp_bind (mkkey _); iApply wp_mkkey; wp_pures.
wp_hash; wp_tenc; wp_pures.
wp_list; wp_term_of_list; wp_pures.
wp_bind (session_key_of_key_exch _); iApply wp_session_key_of_key_exch.
wp_bind (mkkey _); iApply wp_mkkey; wp_pures.
by wp_tenc; wp_pures; wp_list; wp_term_of_list.
Qed.

Definition opterm (ot : option term) : iProp :=
  match ot with
  | Some t => pterm t
  | None => True
  end.

Global Instance persistent_opterm ot : Persistent (opterm ot).
Proof. apply _. Qed.

(* TODO: Strengthen *)
Lemma wp_mkkex (psk : option term) (dh : option term) E Φ :
  opterm psk -∗
  opterm dh -∗
  (∀ okex : option _,
      opterm (S.ser_key_exch_prop <$> okex) -∗
      Φ (repr (S.term_of_key_exch_prop <$> okex))) -∗
  WP mkkex (repr psk) (repr dh) @ E {{ Φ }}.
Proof.
iIntros "#p_psk #p_dh post"; rewrite /mkkex; wp_pures.
case: psk dh => [psk|] [g|] //=; wp_pures.
- wp_bind (mknonce _); iApply (wp_mknonce _ (λ _, True)%I).
  iIntros (a) "#s_a #pred_a token"; wp_pures.
  wp_list; wp_term_of_list; wp_tag; wp_pures.
  iApply ("post" $! (Some (S.PskDhP psk g (TNonce a)))).
  rewrite /= pterm_tag pterm_of_list /=; do !iSplit => //.
  + by rewrite pterm_THash; eauto.
  + by rewrite pterm_TExp; eauto.
  + rewrite pterm_TExp1 pterm_TExp0; iLeft; iSplit; eauto.
    by rewrite pterm_TNonce; iExists _; eauto.
- wp_tag; wp_pures.
  iApply ("post" $! (Some (S.PskP psk))).
  by rewrite /= pterm_tag pterm_THash; eauto.
- wp_bind (mknonce _); iApply (wp_mknonce _ (λ _, True)%I).
  iIntros (a) "#s_a #pred_a token"; wp_pures.
  wp_list; wp_term_of_list; wp_tag; wp_pures.
  iApply ("post" $! (Some (S.DhP g (TNonce a)))).
  rewrite /= pterm_tag pterm_of_list /=; do !iSplit => //.
  + by rewrite pterm_TExp; eauto.
  + rewrite pterm_TExp1 pterm_TExp0; iLeft; iSplit; eauto.
    by rewrite pterm_TNonce; iExists _; eauto.
- by iApply ("post" $! None).
Qed.

Definition client : val := λ: "psk" "dh" "hash_alg" "ae_alg",
  bind: "kex" := mkkex "psk" "dh" in
  let: "nonce" := mknonce #() in
  let: "params" :=
    term_of_list [S.tls13; "nonce"; "kex"; "hash_alg"; "ae_alg"] in
  let: "ch" := client_hello "params" in
  send "ch";;
  let: "sh" := recv #() in


Lemma wp_client psk dh hash_alg ae_alg E :
  opterm psk -∗
  opterm dh -∗
  pterm hash_alg -∗
  pterm ae_alg -∗
  WP client (repr psk) (repr dh) hash_alg ae_alg @ E {{ _, True }}.
Proof.
iIntros "#p_psk #p_dh #p_h #p_ae".
rewrite /client; wp_pures.
wp_bind (mkkex _ _); iApply wp_mkkex => //.
iIntros (kex) "#p_kex"; case: kex => [kex|]; wp_pures => //=.
wp_bind (mknonce _); iApply (wp_mknonce _ (λ _, True)%I).
iIntros (a) "_ #pred_a token".
wp_pures; wp_list; wp_term_of_list.
wp_pures; wp_bind (client_hello _).
iApply (wp_client_hello (S.ClientParams S.tls13 (TNonce a) kex hash_alg ae_alg)).
wp_pures; iApply wp_send => //.
iModIntro.
do !rewrite !pterm_of_list /=.
iSplit.
  rewrite pterm_TInt; iSplit => //.
  rewrite pterm_TNonce; iSplit => //.
    by iExists _; iSplit; eauto.
  by do !iSplit => //.
iSplit => //.

end I.

End I.
