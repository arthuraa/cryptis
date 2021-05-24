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
Definition tls12 := TInt 2.
Definition tls13 := TInt 3.

Definition dhe_13 g gx :=
  Spec.tag (tlsN.@"dhe_13") (Spec.of_list [g; gx]).

Definition is_dhe_13 t :=
  if Spec.untag (tlsN.@"dhe_13") t isn't Some t then None
  else Spec.to_list t.

Definition hmac k t :=
  THash (Spec.of_list [k; t]).

Notation prf := hmac (only parsing).
Notation hkdf_extract := prf (only parsing).

Definition hkdf_expand_label k (l : string) t :=
  prf k (Spec.tag (nroot.@l) t).

Definition derive_secret k l t :=
  hkdf_expand_label k l (THash t).

Definition kdf_es psk :=
  let es := hmac zero psk in
  let kb := derive_secret es "tls13_resumption_psk_binder_key" zero in
  (es, kb).

Definition kdf_k0 es log :=
  let atcs0 := derive_secret es "tls13_client_early_traffic_secret" log in
  let kc0 := hkdf_expand_label atcs0 "tls13_key" zero in
  let ems0 := derive_secret es "tls13_early_exporter_master_secret" log in
  (kc0, ems0).

Notation kdf_hs := hkdf_extract (only parsing).

Definition kdf_ms hs log :=
  let ms   := hkdf_extract hs zero in
  let htsc := derive_secret hs "tls13_client_handshake_traffic_secret" log in
  let htss := derive_secret hs "tls13_server_handshake_traffic_secret" log in
  let kch  := hkdf_expand_label htsc "tls13_key" zero in
  let kcm  := hkdf_expand_label htsc "tls13_finished" zero in
  let ksh  := hkdf_expand_label htss "tls13_key" zero in
  let ksm  := hkdf_expand_label htss "tls13_finished" zero in
  [ms; kch; ksh; kcm; ksm].

Definition kdf_k ms log :=
  let atsc := derive_secret ms "tls13_client_application_traffic_secret" log in
  let atss := derive_secret ms "tls13_server_application_traffic_secret" log in
  let ems  := derive_secret ms "tls13_exporter_master_secret" log in
  let kc   := hkdf_expand_label atsc "tls13_key" zero in
  let ks   := hkdf_expand_label atss "tls13_key" zero in
  [kc; ks; ems].

Definition kdf_psk ms log :=
  derive_secret ms "tls13_resumption_master_secret" log.

Definition client13_offer psk g gx hash_alg ae_alg cr :=
  let '(early_secret, kb) := kdf_es psk in
  let zoffer := Spec.of_list [tls13; dhe_13 g gx; hash_alg; ae_alg; zero] in
  let pt := hmac kb (Spec.of_list [cr; zoffer]) in
  let offer := Spec.of_list [tls13; dhe_13 g gx; hash_alg; ae_alg; pt] in
  let ch := Spec.of_list [cr; offer] in
  let '(kc0, ems0) := kdf_k0 early_secret ch in
  [ch; early_secret; kc0; ems0].

Definition client13_check_mode early_secret g x ch sh :=
  if Spec.to_list sh isn't Some sh' then None else
  if prod_of_list 2 sh' isn't Some (sr, mode) then None
  else if Spec.to_list mode isn't Some mode then None
  else if prod_of_list 5 mode isn't
    Some (version, kex_alg', hash_alg', ae_alg', spt) then None
  else if is_dhe_13 kex_alg' isn't Some kex_alg' then None
  else if prod_of_list 2 kex_alg' isn't Some (g', gy) then None
  else if negb (bool_decide (version = S.tls13 ∧ g' = g)) then None
  else let log := Spec.of_list [ch; sh] in
  let gxy := Spec.texp gy x in
  let handshake_secret := kdf_hs early_secret gxy in
  if kdf_ms handshake_secret log isn't [master_secret; chk; shk; cfin; sfin] then None
  else Some [log; master_secret; chk; shk; cfin; sfin].

Definition mkhash (hash_alg : term) x :=
  THash (Spec.of_list [hash_alg; x]).

Definition verify verif_key x sig :=
  match Spec.tdec (tlsN.@"sign") verif_key sig with
  | Some x' => bool_decide (x = x')
  | None => false
  end.

Definition client13_check_sig
  master_secret log hash_alg sfin cfin verif_key sig m1 :=
  if Spec.is_key verif_key isn't Some Dec then None
  else let log := Spec.of_list [log; verif_key] in
  if negb (verify verif_key (mkhash hash_alg log) sig) then None
  else let log := Spec.of_list [log; sig] in
  if negb (bool_decide (m1 = hmac sfin log)) then None
  else let log := Spec.of_list [log; m1] in
  if prod_of_list 3 (kdf_k master_secret log) isn't Some (cak, sak, ems) then None
  else let m2 := hmac cfin log in
  let log := Spec.of_list [log; m2] in
  let rms := kdf_psk master_secret log in
  Some [m2; cak; sak; ems; rms].

Definition server13_check_offer (ch psk : term) : option (term * term) :=
  ch' ← Spec.to_list ch;
  '(cr, offer) ← prod_of_list 2 ch';
  offer ← Spec.to_list offer;
  '(version, g, gx, hash_alg, ae_alg, m) ← prod_of_list 6 offer;
  if negb (bool_decide (version = tls13)) then None
  else let '(early_secret, kb) := kdf_es psk in
  let zoffer := Spec.of_list [tls13; g; gx; hash_alg; ae_alg; zero] in
  if negb (bool_decide (m = hmac kb (Spec.of_list [cr; zoffer]))) then None
  else Some (kdf_k0 early_secret ch).

Definition server13_mode sr g gy hash_alg ae_alg pt :=
  let mode := Spec.of_list [tls13; dhe_13 g gy; hash_alg; ae_alg; pt] in
  Spec.of_list [sr; mode].

End S.

Module I.

Section I.

Context `{!heapG Σ, !cryptoG Σ, !network Σ}.
Notation iProp := (iProp Σ).

Implicit Types t : term.
Implicit Types s : session_view.
Implicit Types rl : role.
Implicit Types Φ : val → iProp.

Definition dhe_13 : val := λ: "g" "gx",
  tag (tlsN.@"dhe_13") (term_of_list ["g"; "gx"]).

Lemma wp_dhe_13 E g gx Φ :
  Φ (S.dhe_13 g gx) -∗
  WP dhe_13 g gx @ E {{ Φ }}.
Proof.
rewrite /dhe_13; iIntros "post".
by wp_list; wp_term_of_list; wp_tag.
Qed.

Definition is_dhe_13 : val := λ: "t",
  bind: "t" := untag (tlsN.@"dhe_13") "t" in
  list_of_term "t".

Lemma wp_is_dhe_13 E t Φ :
  Φ (repr (S.is_dhe_13 t)) -∗
  WP is_dhe_13 t @ E {{ Φ }}.
Proof.
rewrite /S.is_dhe_13 /is_dhe_13; iIntros "post".
wp_untag_eq t' e; last by rewrite e; wp_pures.
rewrite {}e Spec.tagK; wp_list_of_term_eq ts e; last by rewrite e.
by rewrite {}e Spec.of_listK.
Qed.

Definition hmac : val := λ: "k" "x",
  hash (term_of_list ["k"; "x"]).

Lemma wp_hmac E t1 t2 Φ :
  Φ (S.hmac t1 t2) -∗
  WP hmac t1 t2 @ E {{ Φ }}.
Proof.
rewrite /hmac.
iIntros "post"; wp_pures.
wp_list; wp_term_of_list.
by iApply wp_hash.
Qed.

Notation prf := hmac (only parsing).

Notation hkdf_extract := prf (only parsing).

Definition hkdf_expand_label (l : string) : val := λ: "k" "h",
  prf "k" (tag (nroot.@l) "h").

Lemma wp_hkdf_expand_label E l t1 t2 Φ :
  Φ (S.hkdf_expand_label t1 l t2) -∗
  WP hkdf_expand_label l t1 t2 @ E {{ Φ }}.
Proof.
rewrite /hkdf_expand_label; iIntros "post"; wp_pures.
wp_tag; by iApply wp_hmac.
Qed.

Definition derive_secret l : val := λ: "k" "m",
  hkdf_expand_label l "k" (hash "m").

Lemma wp_derive_secret E l t1 t2 Φ :
  Φ (S.derive_secret t1 l t2) -∗
  WP derive_secret l t1 t2 @ E {{ Φ }}.
Proof.
rewrite /derive_secret; iIntros "post"; wp_pures.
by wp_hash; iApply wp_hkdf_expand_label.
Qed.

Definition kdf_es : val := λ: "psk",
  let: "es" := hkdf_extract S.zero "psk" in
  let: "kb" := derive_secret "tls13_resumption_psk_binder_key" "es" S.zero in
  ("es", "kb").

Lemma wp_kdf_es E psk Φ :
  Φ (repr (S.kdf_es psk)) -∗
  WP kdf_es psk @ E {{ Φ }}.
Proof.
rewrite /kdf_es; iIntros "post"; wp_pures.
wp_bind (hmac _ _); iApply wp_hmac; wp_pures.
by wp_bind (derive_secret _ _ _); iApply wp_derive_secret; wp_pures.
Qed.

Definition kdf_k0 : val := λ: "es" "log",
  let: "atsc0" := derive_secret "tls13_client_early_traffic_secret" "es" "log" in
  let: "kc0"   := hkdf_expand_label "tls13_key" "atsc0" S.zero in
  let: "ems0"  := derive_secret "tls13_early_exporter_master_secret" "es" "log" in
  ("kc0", "ems0").

Lemma wp_kdf_k0 E es log Φ :
  Φ (repr (S.kdf_k0 es log)) -∗
  WP kdf_k0 es log @ E {{ Φ }}.
Proof.
rewrite /kdf_k0; iIntros "post"; wp_pures.
wp_bind (derive_secret _ _ _); iApply wp_derive_secret; wp_pures.
wp_bind (hkdf_expand_label _ _ _); iApply wp_hkdf_expand_label; wp_pures.
by wp_bind (derive_secret _ _ _); iApply wp_derive_secret; wp_pures.
Qed.

Notation kdf_hs := hkdf_extract (only parsing).

Definition kdf_ms :val := λ: "hs" "log",
  let: "ms" := hkdf_extract "hs" S.zero in
  let: "htsc" :=
    derive_secret "tls13_client_handshake_traffic_secret" "hs" "log" in
  let: "htss" :=
    derive_secret "tls13_server_handshake_traffic_secret" "hs" "log" in
  let: "kch" :=  hkdf_expand_label "tls13_key" "htsc" S.zero in
  let: "kcm" :=  hkdf_expand_label "tls13_finished" "htsc" S.zero in
  let: "ksh" :=  hkdf_expand_label "tls13_key" "htss" S.zero in
  let: "ksm" :=  hkdf_expand_label "tls13_finished" "htss" S.zero in
  ["ms"; "kch"; "ksh"; "kcm"; "ksm"].

Lemma wp_kdf_ms E hs log Φ :
  Φ (repr (S.kdf_ms hs log)) -∗
  WP kdf_ms hs log @ E {{ Φ }}.
Proof.
rewrite /kdf_ms; iIntros "post"; wp_pures.
wp_bind (hmac _ _); iApply wp_hmac; wp_pures.
wp_bind (derive_secret _ _ _); iApply wp_derive_secret; wp_pures.
wp_bind (derive_secret _ _ _); iApply wp_derive_secret; wp_pures.
wp_bind (hkdf_expand_label _ _ _); iApply wp_hkdf_expand_label; wp_pures.
wp_bind (hkdf_expand_label _ _ _); iApply wp_hkdf_expand_label; wp_pures.
wp_bind (hkdf_expand_label _ _ _); iApply wp_hkdf_expand_label; wp_pures.
wp_bind (hkdf_expand_label _ _ _); iApply wp_hkdf_expand_label; wp_pures.
by wp_list.
Qed.

Definition kdf_k : val := λ: "ms" "log",
  let: "atsc" :=
    derive_secret "tls13_client_application_traffic_secret" "ms" "log" in
  let: "atss" :=
    derive_secret "tls13_server_application_traffic_secret" "ms" "log" in
  let: "ems"  :=
    derive_secret "tls13_exporter_master_secret" "ms" "log" in
  let: "kc"   :=
    hkdf_expand_label "tls13_key" "atsc" S.zero in
  let: "ks"   :=
    hkdf_expand_label "tls13_key" "atss" S.zero in
  ["kc"; "ks"; "ems"].

Lemma wp_kdf_k E ms log Φ :
  Φ (repr (S.kdf_k ms log)) -∗
  WP kdf_k ms log @ E {{ Φ }}.
Proof.
rewrite /kdf_k; iIntros "post"; wp_pures.
wp_bind (derive_secret _ _ _); iApply wp_derive_secret; wp_pures.
wp_bind (derive_secret _ _ _); iApply wp_derive_secret; wp_pures.
wp_bind (derive_secret _ _ _); iApply wp_derive_secret; wp_pures.
wp_bind (hkdf_expand_label _ _ _); iApply wp_hkdf_expand_label; wp_pures.
wp_bind (hkdf_expand_label _ _ _); iApply wp_hkdf_expand_label; wp_pures.
by wp_list.
Qed.

Definition kdf_psk : val := λ: "ms" "log",
  derive_secret "tls13_resumption_master_secret" "ms" "log".

Lemma wp_kdf_psk E ms log Φ :
  Φ (S.kdf_psk ms log) -∗
  WP kdf_psk ms log @ E {{ Φ }}.
Proof.
rewrite /kdf_psk; iIntros "post"; wp_pures.
by iApply wp_derive_secret.
Qed.

Definition dh_keygen : val := λ: "g",
  let: "x" := mknonce #() in
  ["x"; texp "g" "x"].

Definition client13_offer : val := λ: "psk" "g" "gx" "hash_alg" "ae_alg" "cr",
  let: "kdf_es_res" := kdf_es "psk" in
  let: "early_secret" := Fst "kdf_es_res" in
  let: "kb" := Snd "kdf_es_res" in
  let: "zoffer" :=
    term_of_list [S.tls13; dhe_13 "g" "gx"; "hash_alg"; "ae_alg";  S.zero] in
  let: "pt" := hmac "kb" (term_of_list ["cr"; "zoffer"]) in
  let: "offer" :=
    term_of_list [S.tls13; dhe_13 "g" "gx"; "hash_alg"; "ae_alg"; "pt"] in
  let: "ch" := term_of_list ["cr"; "offer"] in
  let: "kdf_k0_res" := kdf_k0 "early_secret" "ch" in
  let: "kc0" := Fst "kdf_k0_res" in
  let: "ems0" := Snd "kdf_k0_res" in
  ["ch"; "early_secret"; "kc0"; "ems0"].

Lemma wp_client13_offer E psk g gx hash_alg ae_alg cr Φ :
  Φ (repr (S.client13_offer psk g gx hash_alg ae_alg cr)) -∗
  WP client13_offer psk g gx hash_alg ae_alg cr @ E {{ Φ }}.
Proof.
rewrite /client13_offer; iIntros "?"; wp_pures.
wp_bind (kdf_es _); iApply wp_kdf_es; wp_pures.
wp_list.
wp_bind (dhe_13 _ _); iApply wp_dhe_13.
wp_list; wp_term_of_list; wp_pures.
wp_list; wp_term_of_list; wp_pures.
wp_bind (hmac _ _); iApply wp_hmac; wp_pures.
wp_list.
wp_bind (dhe_13 _ _); iApply wp_dhe_13.
wp_list; wp_term_of_list.
wp_list; wp_term_of_list; wp_pures.
wp_bind (kdf_k0 _ _); iApply wp_kdf_k0; wp_pures.
by wp_list.
Qed.

(** TODO

Why do we need spt? This information does not seem to be checked or tracked
anywhere, apart from being included in the log.

*)
Definition client13_check_mode : val := λ: "early_secret" "g" "x" "ch" "sh",
  bind: "sh'" := list_of_term "sh" in
  list_match: ["sr"; "mode"] := "sh'" in
  bind: "mode" := list_of_term "mode" in
  list_match: ["version"; "kex_alg"; "h"; "a"; "spt"] := "mode" in
  bind: "kex_alg" := is_dhe_13 "kex_alg" in
  list_match: ["g'"; "gy"] := "kex_alg" in
  assert: eq_term "version" S.tls13 && eq_term "g'" "g" in
  let: "log" := term_of_list ["ch"; "sh"] in
  let: "gxy" := texp "gy" "x" in
  let: "handshake_secret" := kdf_hs "early_secret" "gxy" in
  let: "kdf_ms" := kdf_ms "handshake_secret" "log" in
  list_match: ["master_secret"; "chk"; "shk"; "cfin"; "sfin"] := "kdf_ms" in
  SOME ["log"; "master_secret"; "chk"; "shk"; "cfin"; "sfin"].

Lemma wp_client13_check_mode E early_secret g x ch sh Φ :
  Φ (repr (S.client13_check_mode early_secret g x ch sh)) -∗
  WP client13_check_mode early_secret g x ch sh @ E {{ Φ }}.
Proof.
iIntros "post"; rewrite /client13_check_mode /S.client13_check_mode.
wp_list_of_term_eq sh' e; last by rewrite e; wp_pures.
rewrite {sh}e Spec.of_listK.
wp_list_match => [sr mode {sh'} ->|ne]; last first.
  by rewrite prod_of_list_neq //; wp_finish.
rewrite {1}unlock /=.
wp_list_of_term_eq mode' e; last by rewrite e; wp_pures.
rewrite e Spec.of_listK {e mode}.
wp_list_match => [version kex_alg h a spt {mode'} ->|ne]; last first.
  by rewrite prod_of_list_neq //; wp_finish.
rewrite {1}unlock /=.
wp_bind (is_dhe_13 _); iApply wp_is_dhe_13.
case: S.is_dhe_13 => [kex_alg'|]; last by wp_pures.
wp_list_match => [g' gy {kex_alg'} ->|?]; wp_finish; 
  last by rewrite prod_of_list_neq.
rewrite {1}unlock /=.
wp_eq_term e; last first.
  rewrite bool_decide_decide decide_False //=; last intuition congruence.
  by wp_pures.
rewrite {version}e.
wp_eq_term e; last first.
  rewrite bool_decide_decide decide_False //=; last intuition congruence.
  by wp_pures.
rewrite {g'}e bool_decide_decide decide_True //=.
wp_list; wp_term_of_list.
wp_pures; wp_bind (texp _ _); iApply wp_texp; wp_pures.
wp_bind (hmac _ _); iApply wp_hmac; wp_pures.
wp_bind (kdf_ms _ _); iApply wp_kdf_ms; wp_pures.
wp_list_match => // ????? [] <- <- <- <- <-.
wp_list; by wp_pures.
Qed.

Definition sign : val := λ: "k" "x",
  tenc (tlsN.@"sign") "k" "x".

Definition verify : val := λ: "k" "x" "sig",
  match: tdec (tlsN.@"sign") "k" "sig" with
    SOME "x'" => eq_term "x" "x'"
  | NONE => #false
  end.

Lemma wp_verify k x sig E Φ :
  Φ #(S.verify (TKey Dec k) x sig) -∗
  WP verify (TKey Dec k) x sig @ E {{ Φ }}.
Proof.
rewrite /S.verify /verify; iIntros "p".
wp_tdec_eq x' e; last by rewrite e; wp_pures.
rewrite {}e /Spec.tdec /= decide_True // Spec.tagK; wp_pures.
by wp_eq_term e; rewrite /bool_decide; [rewrite decide_True|rewrite decide_False].
Qed.

Definition mkhash : val := λ: "hash_alg" "m",
  hash (term_of_list ["hash_alg"; "m"]).

Lemma wp_mkhash hash_alg m E Φ :
  Φ (S.mkhash hash_alg m) -∗
  WP mkhash hash_alg m @ E {{ Φ }}.
Proof.
rewrite /mkhash /S.mkhash; iIntros "p".
by wp_list; wp_term_of_list; wp_hash.
Qed.

(**

TLS 1.3 Client

Parameters:

- a: Client identity
- b: Server identity
- psk: pre-shared key between a and b
- g: Diffie-Hellman generator
- aaa: ???
- hhh: ???

*)

Definition client13_check_sig : val :=
λ: "master_secret" "log" "hash_alg" "sfin" "cfin" "verif_key" "sig" "m1",
  bind: "kt" := is_key "verif_key" in
  assert: "kt" = repr Dec in
  let: "log" := term_of_list ["log"; "verif_key"] in
  assert: verify "verif_key" (mkhash "hash_alg" "log") "sig" in
  let: "log" := term_of_list ["log"; "sig"] in
  assert: eq_term "m1" (hmac "sfin" "log") in
  let: "log" := term_of_list ["log"; "m1"] in
  let: "kdf_k_res" := kdf_k "master_secret" "log" in
  list_match: ["cak"; "sak"; "ems"] := "kdf_k_res" in
  let: "m2" := hmac "cfin" "log" in
  let: "log" := term_of_list ["log"; "m2"] in
  let: "rms" := kdf_psk "master_secret" "log" in
  SOME ["m2"; "cak"; "sak"; "ems"; "rms"].

Lemma wp_client13_check_sig
  master_secret log hash_alg sfin cfin verif_key sig m1 E Φ :
  Φ (repr (S.client13_check_sig master_secret log hash_alg
                                sfin cfin verif_key sig m1)) -∗
  WP client13_check_sig master_secret log hash_alg sfin cfin verif_key
       sig m1 @ E {{ Φ }}.
Proof.
rewrite /client13_check_sig /S.client13_check_sig.
iIntros "p".
wp_pures; wp_bind (is_key _); iApply wp_is_key.
case: verif_key; try by move=> * /=; wp_pures.
case=> [] verif_key /=; wp_pures => //=.
wp_list; wp_term_of_list.
wp_pures; wp_bind (mkhash _ _); iApply wp_mkhash.
wp_pures; wp_bind (verify _ _ _); iApply wp_verify.
case: S.verify => /=; wp_pures => //.
wp_list; wp_term_of_list.
wp_pures; wp_bind (hmac _ _); iApply wp_hmac.
wp_eq_term e; last first.
  by rewrite /bool_decide decide_False //=; wp_pures.
rewrite /bool_decide decide_True //= {}e; wp_pures.
wp_list; wp_term_of_list; wp_pures.
wp_bind (kdf_k _ _); iApply wp_kdf_k.
wp_pures.
wp_list_match => //= cak sak ems [<- <- <-].
rewrite [@prod_of_list]unlock /=.
wp_bind (hmac _ _); iApply wp_hmac.
wp_list; wp_term_of_list.
wp_pures; wp_bind (kdf_psk _ _); iApply wp_kdf_psk.
by wp_list; wp_pures.
Qed.

Definition client13 : val := λ: "psk" "g" "hash_alg" "ae_alg",
  let: "cr" := mknonce #() in
  list_match: ["x"; "gx"] := dh_keygen "g" in
  let: "offer" := client13_offer "psk" "g" "gx" "hash_alg" "ae_alg" "cr" in
  list_match: ["ch"; "early_secret"; "kc0"; "ems0"] := "offer" in
  send "ch";;
  (* insert clientSession0(cr,psk,offer,kc0,ems0*)

  let: "sh" := recv #() in
  bind: "check_mode" :=
    client13_check_mode "early_secret" "g" "x" "ch" "sh" in
  list_match: ["log"; "master_secret"; "chk"; "shk"; "cfin"; "sfin"] :=
    "check_mode" in

  let: "verif_key" := recv #() in
  (* get longTermKeys_tbl(sn,xxx,=verif_key)
     ---> Check that the verification key belongs to a server.  *)
  let: "sig" := recv #() in
  let: "m1" := recv #() in
  bind: "check_sig" :=
    client13_check_sig "master_secret" "log" "hash_alg" "sfin" "cfin"
      "verif_key" "sig" "m1" in
  list_match: ["m2"; "cak"; "sak"; "ems"; "rms"] := "check_sig" in
  (* event ClientFinished(TLS13,cr,sr,psk,p,offer,mode,cak,sak,ems,rms) *)
  (* insert clientSession(cr,sr,psk,p,offer,mode,cak,sak,ems,rms) *)
  send "m2".

(**

Parameters:
- a: Client identity
- b: Server identity
- psk: Pre-shared key
*)

Definition server13_check_offer : val := λ: "ch" "psk",
  bind: "ch'" := list_of_term "ch" in
  list_match: ["cr"; "offer"] := "ch'" in
  bind: "offer" := list_of_term "offer" in
  list_match: ["version"; "g"; "gx"; "hash_alg"; "ae_alg"; "m"] := "offer" in
  assert: eq_term "version" S.tls13 in
  let: "kdf_es_res" := kdf_es "psk" in
  let: "early_secret" := Fst "kdf_es_res" in
  let: "kb" := Snd "kdf_es_res" in
  let: "zoffer" := term_of_list [S.tls13; "g"; "gx"; "hash_alg"; "ae_alg"; S.zero] in
  assert: eq_term "m" (hmac "kb" (term_of_list ["cr"; "zoffer"])) in
  SOME (kdf_k0 "early_secret" "ch").

Lemma wp_server13_check_offer ch psk E Ψ :
  Ψ (repr (S.server13_check_offer ch psk)) -∗
  WP server13_check_offer ch psk @ E {{ Ψ }}.
Proof.
rewrite /S.server13_check_offer /server13_check_offer; iIntros "p".
wp_list_of_term_eq ch' e; last by rewrite e /=; wp_pures.
rewrite {}e /= Spec.of_listK /=.
wp_list_match => [cr offer {ch'} ->|ne]; wp_finish; last first.
  by rewrite prod_of_list_neq //=; wp_pures.
rewrite [in prod_of_list 2]unlock /=.
wp_list_of_term_eq offer' e; last first.
  by rewrite {}e /=; wp_pures.
rewrite {}e Spec.of_listK /=.
wp_list_match => [version g gx hash_alg ae_alg m {offer'} ->|ne]; wp_finish; last first.
  by rewrite prod_of_list_neq //=.
rewrite [in prod_of_list 6]unlock /=.
wp_eq_term e; last first.
  by rewrite /bool_decide decide_False //=; wp_pures.
rewrite {}e /=.
wp_pures; wp_bind (kdf_es _); iApply wp_kdf_es.
wp_pures.
wp_list; wp_term_of_list.
wp_pures.
wp_list; wp_term_of_list.
wp_bind (hmac _ _); iApply wp_hmac.
wp_eq_term e; last first.
  by rewrite /bool_decide decide_False //=; wp_pures.
rewrite /bool_decide decide_True //=; wp_pures.
by wp_bind (kdf_k0 _ _); iApply wp_kdf_k0; wp_pures.
Qed.

Definition server13_mode : val := λ: "sr" "g" "gy" "hash_alg" "ae_alg" "pt",
  let: "mode" := term_of_list [tls13; dhe_13 "g" "gy"; "hash_alg"; "ae_alg"; "pt"] in
  term_of_list ["sr"; "mode"].

Definition server13 : val :=
λ: "psk" "xx" "ee" "hash_alg" "ae_alg" "pt" "sign_key" "verif_key",
  let: "ch" := recv #() in
  bind: "check" := server13_check_offer "ch" "psk" in
  let: "kc0" := Fst "check" in
  let: "ems0" := Snd "check" in
  (* insert serverSession0(cr,psk,offer,kc0,ems0); *)

  let: "sr" := mknonce #() in
  let: "dh_res" := dh_keygen "g" in
  let: "y" := Fst "dh_res" in
  let: "gy" := Snd "dh_res" in
  let: "sh" := server13_mode "sr" "g" "gy" "hash_alg" "ae_alg" "pt" in
  send "sh";;
  (* get longTermKeys(sn,sk,p) *)
  (* event ServerChoosesVersion(cr,sr,p,TLS13); *)
  (* event ServerChoosesKEX(cr,sr,p,TLS13,DHE_13(g,gy)); *)
  (* event ServerChoosesAE(cr,sr,p,TLS13,a); *)
  (* event ServerChoosesHash(cr,sr,p,TLS13,h); *)

  let: "log" := term_of_list ["ch"; "sh"] in
  let: "gxy" := texp "gx" "y" in
  let: "handshake_secret" := kdf_hs "early_secret" "gxy" in
  bind: "kdf_ms" := kdf_ms "handshake_secret" "log" in
  list_match: ["master_secret"; "chk"; "shk"; "cfin"; "sfin"] := "kdf_ms" in
  send (term_of_list ["chk"; "shk"]) ;;
  send "verif_key";;
  let: "log" := term_of_list ["log"; "verif_key"] in
  let: "sig" := sign "sign_key" (mkhash "hash_alg" "log") in
  send "sig";;

  let: "log" := term_of_list ["log"; "sig"] in
  let: "m1" := hmac "sfin" "log" in
  let: "log" := term_of_list ["log"; "m1"] in

  bind: "kdf_k_res" := list_of_term (kdf_k "master_secret" "log") in
  list_match: ["cak"; "sak"; "ems"] := "kdf_k_res" in
  (*  event PreServerFinished(TLS13,cr,sr,psk,p,offer,mode,cak,sak,ems) *)
  send "m1";;

  let: "m2" := recv #() in
  assert: "m2" = hmac "cfin" "log" in
  let: "log" := term_of_list ["log"; "m2"] in
  let: "rms" := kdf_psk "master_secret" "log" in
  (* event ServerFinished(TLS13,cr,sr,psk,p,offer,mode,cak,sak,ems,rms); *)
  (* insert serverSession(cr,sr,psk,p,offer,mode,cak,sak,ems,rms); *)
  (* phase 1; *)
  (* event PostSessionCompromisedKey(pk(sk)); *)
  (* out(io,sk)). *)
  #().

End TLS13.
