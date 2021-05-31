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

Variant key_exch_alg :=
| PskA of term
| DhA of term
| PskDhA of term & term.

Definition ser_key_exch_alg ke :=
  match ke with
  | PskA psk => PskA (THash psk)
  | DhA g => DhA g
  | PskDhA psk g => PskDhA (THash psk) g
  end.

Definition term_of_key_exch_alg ke :=
  match ke with
  | PskA psk => Spec.tag (nroot.@"psk") psk
  | DhA g => Spec.tag (nroot.@"dh") g
  | PskDhA psk g => Spec.tag (nroot.@"pskdh") (Spec.of_list [psk; g])
  end.

Variant key_exch_prop :=
| PskP of term & term
| DhP of term & term
| PskDhP of term & term & term.

Definition key_exch_alg_of_prop ke :=
  match ke with
  | PskP psk _ => PskA psk
  | DhP g _ => DhA g
  | PskDhP psk g _ => PskDhA psk g
  end.

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

Definition key_exch_prop_of_term ke :=
  if Spec.untag (nroot.@"psk") ke is Some args then
    args ← Spec.to_list args;
    '(psk, c_nonce) ← prod_of_list 2 args;
    Some (PskP psk c_nonce)
  else if Spec.untag (nroot.@"dh") ke is Some args then
    args ← Spec.to_list args;
    '(g, gx) ← prod_of_list 2 args;
    Some (DhP g gx)
  else if Spec.untag (nroot.@"pskdh") ke is Some args then
    args ← Spec.to_list args;
    '(psk, g, gx) ← prod_of_list 3 args;
    Some (PskDhP psk g gx)
  else None.

Lemma term_of_key_exch_propK ke :
  key_exch_prop_of_term (term_of_key_exch_prop ke) = Some ke.
Proof.
rewrite /key_exch_prop_of_term.
case: ke => [psk c_nonce|g gx|psk g gx] /=.
- by rewrite Spec.tagK Spec.of_listK /= unlock /=.
- rewrite Spec.untag_tag_ne //; try set_solver.
  by rewrite Spec.tagK Spec.of_listK /= unlock /=.
- rewrite Spec.untag_tag_ne //; try set_solver.
- rewrite Spec.untag_tag_ne //; try set_solver.
  by rewrite Spec.tagK Spec.of_listK /= unlock /=.
Qed.

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

Definition check_key_exch_prop psk ke :=
  match ke with
  | PskP psk' _ =>
    if decide (psk' = THash psk) then Some psk else None
  | DhP _ _ => Some zero
  | PskDhP psk' _ _ =>
    if decide (psk' = THash psk) then Some psk else None
  end.

Definition check_client_hello psk other ch :=
  ch ← Spec.to_list ch;
  '(ch, mac) ← prod_of_list 2 ch;
  ch' ← Spec.to_list ch;
  '(ke, other') ← prod_of_list 2 ch';
  ke ← key_exch_prop_of_term ke;
  psk ← check_key_exch_prop psk ke;
  let mac' := thash "binder" [psk; ch] in
  if decide (other' = other ∧ mac' = mac) then Some ke else None.

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

Definition check_server_hello cp sp :=
  sp ← Spec.to_list sp;
  '(pub, sig) ← prod_of_list 2 sp;
  pub' ← Spec.to_list pub;
  '(kex, other) ← prod_of_list 2 pub';
  session_key ← check_session_key (cp_key_exch cp) kex;
  dec_sig ← Spec.tdec (tlsN.@"server_hello") (TKey Dec session_key) sig;
  dec_sig ← Spec.to_list dec_sig;
  '(verif_key, sig) ← prod_of_list 2 dec_sig;
  if decide (other = cp_other cp) then
    if verify (tlsN.@"server_hello_sig") verif_key pub sig then
      Some session_key
    else None
  else None.

Section Properties.

Context `{!heapG Σ, cryptoG Σ}.

(* TODO Prove and strengthen *)
Lemma pterm_client_hello cp :
  pterm (term_of_key_exch_prop (ser_key_exch_prop (cp_key_exch cp))) -∗
  pterm (cp_other cp) -∗
  pterm (client_hello cp).
Proof.
Admitted.

End Properties.

End S.

Module I.

Section I.

Context `{!heapG Σ, !cryptoG Σ, !network Σ}.
Notation iProp := (iProp Σ).

Implicit Types t : term.
Implicit Types s : session_view.
Implicit Types rl : role.
Implicit Types Φ : val → iProp.

Definition key_exch_alg_match : val := λ: "ke" "f_psk" "f_dh" "f_pskdh",
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

Lemma wp_key_exch_alg_match ke (f_psk f_dh f_pskdh : val) E Φ :
  match ke with
  | S.PskA psk => WP f_psk psk @ E {{ Φ }}
  | S.DhA g => WP f_dh g @ E {{ Φ }}
  | S.PskDhA psk g => WP f_pskdh psk g @ E {{ Φ }}
  end -∗
  WP key_exch_alg_match (S.term_of_key_exch_alg ke) f_psk f_dh f_pskdh
     @ E {{ Φ }}.
Proof.
iIntros "post"; rewrite /key_exch_alg_match.
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

Definition is_key_exch_prop : val := λ: "ke",
  match: untag (nroot.@"psk") "ke" with SOME "args" =>
    bind: "args" := list_of_term "args" in
    list_match: ["psk"; "c_nonce"] := "args" in
    SOME "ke"
  | NONE =>
  match: untag (nroot.@"dh") "ke" with SOME "args" =>
    bind: "args" := list_of_term "args" in
    list_match: ["g"; "gx"] := "args" in
    SOME "ke"
  | NONE =>
  match: untag (nroot.@"pskdh") "ke" with SOME "args" =>
    bind: "args" := list_of_term "args" in
    list_match: ["psk"; "g"; "gx"] := "args" in
    SOME "ke"
  | NONE => NONE
  end end end.

Lemma wp_is_key_exch_prop ke E Φ :
  Φ (repr (S.term_of_key_exch_prop <$> S.key_exch_prop_of_term ke)) -∗
  WP is_key_exch_prop ke @ E {{ Φ }}.
Proof.
iIntros "?"; rewrite /S.term_of_key_exch_prop /S.key_exch_prop_of_term.
rewrite /is_key_exch_prop /=; wp_pures.
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
by rewrite {}e.
Qed.

Definition check_key_exch_prop : val := λ: "psk" "ke",
  key_exch_prop_match "ke"
    (λ: "psk'" <>,
        if: eq_term "psk'" (hash "psk") then SOME "psk" else NONE)
    (λ: <> <>, SOME S.zero)
    (λ: "psk'" <> <>,
        if: eq_term "psk'" (hash "psk") then SOME "psk" else NONE).

Lemma wp_check_key_exch_prop psk ke E Φ :
  Φ (repr (S.check_key_exch_prop psk ke)) -∗
  WP check_key_exch_prop psk (S.term_of_key_exch_prop ke) @ E {{ Φ }}.
Proof.
iIntros "?"; rewrite /check_key_exch_prop; wp_pures.
iApply wp_key_exch_prop_match.
case: ke => [psk' c_nonce|g gx|psk' g gx] //=; wp_pures => //.
- wp_hash; wp_eq_term e; wp_pures; try by rewrite decide_False.
  by rewrite decide_True //=.
- wp_hash; wp_eq_term e; wp_pures; try by rewrite decide_False.
  by rewrite decide_True //=.
Qed.

Definition check_client_hello : val := λ: "psk" "other" "ch",
  bind: "ch" := list_of_term "ch" in
  list_match: ["ch"; "mac"] := "ch" in
  bind: "ch'" := list_of_term "ch" in
  list_match: ["ke"; "other'"] := "ch'" in
  bind: "ke" := is_key_exch_prop "ke" in
  bind: "psk" := check_key_exch_prop "psk" "ke" in
  let: "mac'" := thash "binder" ["psk"; "ch"] in
  if: eq_term "other'" "other" && eq_term "mac'" "mac" then SOME "ke" else NONE.

Lemma wp_check_client_hello psk other ch E Φ :
  Φ (repr (S.term_of_key_exch_prop <$> S.check_client_hello psk other ch)) -∗
  WP check_client_hello psk other ch @ E {{ Φ }}.
Proof.
iIntros "?"; rewrite /check_client_hello /S.check_client_hello.
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
wp_bind (is_key_exch_prop _); iApply wp_is_key_exch_prop.
case e: S.key_exch_prop_of_term => [ke'|] //=; wp_pures => //.
wp_bind (check_key_exch_prop _ _); iApply wp_check_key_exch_prop.
case: S.check_key_exch_prop => [psk'|] /=; wp_pures => //.
wp_list; wp_bind (thash _ _); iApply wp_thash; wp_pures.
wp_eq_term e'; wp_pures; last first.
  rewrite decide_False //; intuition congruence.
rewrite {}e' {other'}.
wp_eq_term e'; wp_pures; last first.
  rewrite decide_False //; intuition congruence.
by rewrite {}e' decide_True //.
Qed.

Definition check_session_key : val := λ: "c_kex" "s_kex",
  key_exch_prop_match "c_kex"
    (λ: "psk" "c_nonce",
      bind: "s_kex" := untag (nroot.@"psk") "s_kex" in
      bind: "s_kex" := list_of_term "s_kex" in
      list_match: ["psk'"; "c_nonce'"; "s_nonce"] := "s_kex" in
      if: eq_term "psk'" (hash "psk") && eq_term "c_nonce'" "c_nonce" then
        SOME (term_of_list ["psk"; "c_nonce"; "s_nonce"])
      else NONE)
    (λ: "g" "x",
      bind: "s_kex" := untag (nroot.@"dh") "s_kex" in
      bind: "s_kex" := list_of_term "s_kex" in
      list_match: ["g'"; "gx"; "gy"] := "s_kex" in
      if: eq_term "g'" "g" && eq_term "gx" (texp "g" "x") then
        SOME (texp "gy" "x")
      else NONE)
    (λ: "psk" "g" "x",
      bind: "s_kex" := untag (nroot.@"pskdh") "s_kex" in
      bind: "s_kex" := list_of_term "s_kex" in
      list_match: ["psk'"; "g'"; "gx"; "gy"] := "s_kex" in
      if: eq_term "psk'" (hash "psk") &&
          eq_term "g'" "g" && eq_term "gx" (texp "g" "x") then
        SOME (texp "gy" "x")
      else NONE).

Lemma wp_check_session_key c_kex s_kex E Φ :
  Φ (repr (S.check_session_key c_kex s_kex)) -∗
  WP check_session_key (S.term_of_key_exch_prop c_kex) s_kex @ E {{ Φ }}.
Proof.
iIntros "?"; rewrite /check_session_key; wp_pures.
iApply wp_key_exch_prop_match.
case: c_kex => [psk c_nonce|g x|psk g x] /=; wp_pures.
- wp_untag_eq s_kex' e; last by wp_pures; rewrite e.
  rewrite {}e Spec.tagK /=.
  wp_list_of_term_eq l e; last by wp_pures; rewrite e.
  rewrite {}e Spec.of_listK /=.
  wp_list_match => [psk' c_nonce' s_nonce ->|ne] //=; wp_finish; last first.
    by rewrite prod_of_list_neq //=.
  rewrite unlock /=.
  wp_hash; wp_eq_term e; last first.
    rewrite decide_False; try by intuition congruence.
    by wp_pures.
  rewrite {}e; wp_eq_term e; last first.
    rewrite decide_False; try by intuition congruence.
    by wp_pures.
  rewrite e decide_True //; wp_pures.
  by wp_list; wp_term_of_list; wp_pures.
- wp_untag_eq s_kex' e; last by wp_pures; rewrite e.
  rewrite {}e Spec.tagK /=.
  wp_list_of_term_eq l e; last by wp_pures; rewrite e.
  rewrite {}e Spec.of_listK /=.
  wp_list_match => [g' gx gy ->|ne] //=; wp_finish; last first.
    by rewrite prod_of_list_neq //=.
  rewrite unlock /=.
  wp_eq_term e; last first.
    rewrite decide_False; try by intuition congruence.
    by wp_pures.
  rewrite {}e; wp_pures; wp_bind (texp _ _); iApply wp_texp.
  wp_eq_term e; last first.
    rewrite decide_False; try by intuition congruence.
    by wp_pures.
  rewrite e decide_True //; wp_pures.
  by wp_pures; wp_bind (texp _ _); iApply wp_texp; wp_pures.
- wp_untag_eq s_kex' e; last by wp_pures; rewrite e.
  rewrite {}e Spec.tagK /=.
  wp_list_of_term_eq l e; last by wp_pures; rewrite e.
  rewrite {}e Spec.of_listK /=.
  wp_list_match => [psk' g' gx gy ->|ne] //=; wp_finish; last first.
    by rewrite prod_of_list_neq //=.
  rewrite unlock /=.
  wp_hash; wp_eq_term e; last first.
    rewrite decide_False; try by intuition congruence.
    by wp_pures.
  rewrite {}e; wp_eq_term e; last first.
    rewrite decide_False; try by intuition congruence.
    by wp_pures.
  rewrite {}e; wp_pures; wp_bind (texp _ _); iApply wp_texp.
  wp_eq_term e; last first.
    rewrite decide_False; try by intuition congruence.
    by wp_pures.
  rewrite e decide_True //; wp_pures.
  by wp_pures; wp_bind (texp _ _); iApply wp_texp; wp_pures.
Qed.

Definition verify N : val := λ: "k" "x" "sig",
  match: tdec N "k" "sig" with
    SOME "y" => eq_term "y" (hash "x")
  | NONE => #false
  end.

Lemma wp_verify N k x sig E Φ :
  Φ #(S.verify N k x sig) -∗
  WP verify N k x sig @ E {{ Φ }}.
Proof.
iIntros "?"; rewrite /verify; wp_pures.
wp_bind (tdec _ _ _); iApply wp_tdec.
rewrite /S.verify; case e: Spec.tdec => [y|]; wp_pures => //.
by wp_hash; iApply wp_eq_term.
Qed.

Definition check_server_hello : val := λ: "cp" "sh",
  bind: "cp" := list_of_term "cp" in
  list_match: ["c_kex"; "c_other"] := "cp" in
  bind: "sh" := list_of_term "sh" in
  list_match: ["pub"; "sig"] := "sh" in
  bind: "pub'" := list_of_term "pub" in
  list_match: ["s_kex"; "s_other"] := "pub'" in
  bind: "session_key" := check_session_key "c_kex" "s_kex" in
  let: "sk" := mkkey "session_key" in
  bind: "dec_sig" := tdec (tlsN.@"server_hello") (Snd "sk") "sig" in
  bind: "dec_sig" := list_of_term "dec_sig" in
  list_match: ["verif_key"; "sig"] := "dec_sig" in
  if: eq_term "s_other" "c_other" then
    if: verify (tlsN.@"server_hello_sig") "verif_key" "pub" "sig" then
      SOME "session_key"
    else NONE
  else NONE.

Lemma wp_check_server_hello cp sh E Φ :
  Φ (repr (S.check_server_hello cp sh)) -∗
  WP check_server_hello (S.term_of_client_params cp) sh @ E {{ Φ }}.
Proof.
iIntros "?"; rewrite /check_server_hello /S.check_server_hello; wp_pures.
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
wp_bind (check_session_key _ _); iApply wp_check_session_key.
case: S.check_session_key => [session_key|]; wp_pures => //=.
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
wp_bind (verify _ _ _ _); iApply wp_verify.
by case: S.verify; wp_pures.
Qed.

Definition opterm (ot : option term) : iProp :=
  match ot with
  | Some t => pterm t
  | None => True
  end.

Global Instance persistent_opterm ot : Persistent (opterm ot).
Proof. apply _. Qed.

Definition mk_key_exch_prop : val := λ: "ke",
  key_exch_alg_match "ke"
    (λ: "psk", tag (nroot.@"psk") (term_of_list ["psk"; mknonce #()]))
    (λ: "g", tag (nroot.@"dh") (term_of_list ["g"; mknonce #()]))
    (λ: "psk" "g", tag (nroot.@"pskdh") (term_of_list ["psk"; "g"; mknonce #()])).

(* TODO: strengthen *)
Lemma wp_mk_key_exch_prop ke E Φ :
  pterm (S.term_of_key_exch_alg (S.ser_key_exch_alg ke)) -∗
  (∀ ke', ⌜ke = S.key_exch_alg_of_prop ke'⌝ →
          pterm (S.term_of_key_exch_prop (S.ser_key_exch_prop ke')) →
          Φ (S.term_of_key_exch_prop ke')) -∗
  WP mk_key_exch_prop (S.term_of_key_exch_alg ke) @ E {{ Φ }}.
Proof.
iIntros "#p_ke post"; rewrite /mk_key_exch_prop; wp_pures.
iApply wp_key_exch_alg_match; case: ke => [psk|g|psk g]; wp_pures.
- wp_bind (mknonce _); iApply (wp_mknonce _ (λ _, True)%I).
  iIntros (a) "_ #pred_a _"; wp_list; wp_term_of_list.
  wp_tag.
  iApply ("post" $! (S.PskP psk (TNonce a))) => //.
  rewrite !pterm_tag pterm_of_list /=.
  do !iSplit => //.
  rewrite pterm_TNonce; by iExists _; iSplit; eauto.
- wp_bind (mknonce _); iApply (wp_mknonce _ (λ _, True)%I).
  iIntros (a) "_ #pred_a _"; wp_list; wp_term_of_list.
  wp_tag.
  iApply ("post" $! (S.DhP g (TNonce a))) => //=.
  rewrite !pterm_tag pterm_of_list /=.
  do !iSplit => //.
  iApply pterm_texp => //.
  rewrite pterm_TNonce; by iExists _; iSplit; eauto.
- wp_bind (mknonce _); iApply (wp_mknonce _ (λ _, True)%I).
  iIntros (a) "_ #pred_a _"; wp_list; wp_term_of_list.
  wp_tag.
  iApply ("post" $! (S.PskDhP psk g (TNonce a))) => //.
  rewrite !pterm_tag !pterm_of_list /=.
  iDestruct "p_ke" as "(? & ? & _)".
  do !iSplit => //.
  iApply pterm_texp => //.
  rewrite pterm_TNonce; by iExists _; iSplit; eauto.
Qed.

Definition client : val := λ: "kex" "other",
  let: "kex" := mk_key_exch_prop "kex" in
  let: "cp"  := term_of_list ["kex"; "other"] in
  let: "ch"  := client_hello "cp" in
  send "ch";;
  let: "sh" := recv #() in
  check_server_hello "cp" "sh".

Lemma wp_client ke other E Φ :
  pterm (S.term_of_key_exch_alg (S.ser_key_exch_alg ke)) -∗
  pterm other -∗
  (∀ cp sh,
      ⌜ke = S.key_exch_alg_of_prop (S.cp_key_exch cp)⌝ →
      ⌜other = S.cp_other cp⌝ →
      pterm sh →
      Φ (repr (S.check_server_hello cp sh))) -∗
  WP client (S.term_of_key_exch_alg ke) other @ E {{ Φ }}.
Proof.
iIntros "#p_ke #p_other post".
rewrite /client; wp_pures.
wp_bind (mk_key_exch_prop _); iApply wp_mk_key_exch_prop => //.
iIntros (ke' e) "#p_ke'"; wp_pures.
wp_list; wp_term_of_list.
wp_pures; wp_bind (client_hello _).
pose cp := {| S.cp_key_exch := ke'; S.cp_other := other |}.
iApply (wp_client_hello cp).
wp_pures; wp_bind (send _); iApply wp_send.
  by iModIntro; iApply S.pterm_client_hello => //.
wp_pures; wp_bind (recv _); iApply wp_recv.
iIntros (sh) "p_sh"; wp_pures.
iApply (wp_check_server_hello cp).
by iApply "post" => //.
Qed.

End I.

End I.
