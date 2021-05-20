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
wp_list (_ :: _ :: []); wp_term_of_list.
wp_tenc; wp_list (_ :: _ :: []); wp_term_of_list.
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
rewrite {t}e repr_list_eq.
case: ts => [|ad [|m [|??]]] /=; wp_pures; try by failure.
wp_hash.
rewrite pterm_of_list /=; iDestruct "p_t" as "(p_ad & p_m & _)".
wp_tdec m; last by failure.
wp_list_of_term_eq m' e; last by failure.
rewrite {m}e repr_list_eq.
case: m' => [|h' [|payload [|??]]]; wp_pures; try by failure.
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

Module S.

Definition zero : term := TInt 0.
Definition tls12 := TInt 2.
Definition tls13 := TInt 3.

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

Definition client13_offer psk g gx aaa hhh cr :=
  let '(early_secret, kb) := kdf_es psk in
  let zoffer := Spec.of_list [tls13; g; gx; aaa; hhh; zero] in
  let pt := hmac kb (Spec.of_list [cr; zoffer]) in
  let offer := Spec.of_list [tls13; g; gx; aaa; hhh; pt] in
  let ch := Spec.of_list [cr; offer] in
  let '(kc0, ems0) := kdf_k0 early_secret ch in
  [ch; kc0; ems0].

End S.

Module I.

Section I.

Context `{!heapG Σ, !cryptoG Σ, !network Σ}.
Notation iProp := (iProp Σ).

Implicit Types t : term.
Implicit Types s : session_view.
Implicit Types rl : role.
Implicit Types Φ : val → iProp.

Definition hmac : val := λ: "k" "x",
  hash (term_of_list ["k"; "x"]).

Lemma wp_hmac E t1 t2 Φ :
  Φ (S.hmac t1 t2) -∗
  WP hmac t1 t2 @ E {{ Φ }}.
Proof.
rewrite /hmac.
iIntros "post"; wp_pures.
wp_list (_ :: _ :: []); wp_term_of_list.
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
by wp_list (_ :: _ :: _ :: _ :: _ :: []).
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
by wp_list (_ :: _ :: _ :: []).
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

Definition client13_offer : val := λ: "psk" "g" "gx" "aaa" "hhh" "cr",
  let: "kdf_es_res" := kdf_es "psk" in
  let: "early_secret" := Fst "kdf_es_res" in
  let: "kb" := Snd "kdf_es_res" in
  let: "zoffer" := term_of_list [S.tls13; "g"; "gx"; "aaa"; "hhh";  S.zero] in
  let: "pt" := hmac "kb" (term_of_list ["cr"; "zoffer"]) in
  let: "offer" := term_of_list [S.tls13; "g"; "gx"; "aaa"; "hhh"; "pt"] in
  let: "ch" := term_of_list ["cr"; "offer"] in
  let: "kdf_k0_res" := kdf_k0 "early_secret" "ch" in
  let: "kc0" := Fst "kdf_k0_res" in
  let: "ems0" := Snd "kdf_k0_res" in
  ["ch"; "kc0"; "ems0"].

Lemma wp_client13_offer E psk g gx aaa hhh cr Φ :
  Φ (repr (S.client13_offer psk g gx aaa hhh cr)) -∗
  WP client13_offer psk g gx aaa hhh cr @ E {{ Φ }}.
Proof.
rewrite /client13_offer; iIntros "?"; wp_pures.
wp_bind (kdf_es _); iApply wp_kdf_es; wp_pures.
wp_list (_ :: _ :: _ :: _ :: _ :: _ :: []); wp_term_of_list; wp_pures.
wp_list (_ :: _ :: []); wp_term_of_list; wp_pures.
wp_bind (hmac _ _); iApply wp_hmac; wp_pures.
wp_list (_ :: _ :: _ :: _ :: _ :: _ :: []); wp_term_of_list; wp_pures.
wp_list (_ :: _ :: []); wp_term_of_list; wp_pures.
wp_bind (kdf_k0 _ _); iApply wp_kdf_k0; wp_pures.
by wp_list (_ :: _ :: _ :: []).
Qed.

Definition tlsN := nroot.@"tls".

Definition sign (mt : string) : val := λ: "k" "x",
  tenc (tlsN.@mt) "k" "x".

Definition verify (mt : string) : val := λ: "k" "x" "s",
  match: tdec (tlsN.@mt) with
    SOME "x'" => "x'" = "x"
  | NONE => #false
  end.

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

Definition client13 : val := λ: "a" "b" "psk" "g" "aaa" "hhh",
  let: "cr" := mknonce #() in
  let: "dh_res" := dh_keygen "g" in
  let: "x" := Fst "dh_res" in
  let: "gx" := Snd "dh_res" in




  let: "kdf_es_res" := kdf_es "psk" in
  let: "early_secret" := Fst "kdf_es_res" in
  let: "kb" := Snd "kdf_es_res" in
  let: "zoffer" := term_of_list [tls13; "g"; "gx"; "aaa"; "hhh";  zero] in
  let: "pt" := hmac "kb" (term_of_list ["cr"; "zoffer"]) in
  let: "offer" := term_of_list [tls13; "g"; "gx"; "aaa"; "hhh"; "pt"] in
  let: "ch" := term_of_list ["cr"; "offer"] in
  send "ch";;
  let: "kdf_k0_res" := kdf_k0 "early_secret" "ch" in
  let: "kc0" := Fst "kdf_k0_res" in
  let: "ems0" := Snd "kdf_k0_res" in
  (* insert clientSession0(cr,psk,offer,kc0,ems0*)

  let: "sh" := recv #() in
  bind: "sh'" := list_of_term "sh" in
  list_match: ["sr"; "mode"] := "sh'" in
  bind: "mode" := list_of_term "mode" in
  list_match: ["version"; "g'"; "gy"; "h"; "a"; "spt"] := "mode" in
  assert: eq_term "version" tls13 && eq_term "g'" "g" in
  let: "log" := term_of_list ["ch"; "sh"] in
  let: "gxy" := texp "gy" "x" in
  let: "handshake_secret" := kdf_hs "early_secret" "gxy" in
  bind: "kdf_ms_res" := list_of_term (kdf_ms "handshake_secret" "log") in
  list_match: ["master_secret"; "chk"; "shk"; "cfin"; "sfin"] := "kdf_ms_res" in
  send (term_of_list ["chk"; "shk"]);;
  let: "p" := recv #() in
  let: "log" := term_of_list ["log"; "p"] in
  (* get longTermKeys_tbl(sn,xxx,=p) *)
  let: "s" := recv #() in
  assert: verify "p" (hash (term_of_list ["h"; "log"])) "s" in
  let: "log" := term_of_list ["log"; "s"] in
  let: "m1" := recv #() in
  assert: eq_term "m1" (hmac "sfin" "log") in
  let: "log" := term_of_list ["log"; "m1"] in
  bind: "kdf_k_res" := list_of_term (kdf_k "master_secret" "log") in
  list_match: ["cak"; "sak"; "ems"] := "kdf_k_res" in
  let: "m2" := hmac "cfin" "log" in
  let: "log" := term_of_list ["log"; "m2"] in
  let: "rms" := kdf_psk "master_secret" "log" in
  (* event ClientFinished(TLS13,cr,sr,psk,p,offer,mode,cak,sak,ems,rms) *)
  (* insert clientSession(cr,sr,psk,p,offer,mode,cak,sak,ems,rms) *)
  send "m".

(**

Parameters:
- a: Client identity
- b: Server identity
- psk: Pre-shared key
*)

Definition server13 : val := λ: "a" "b" "psk" "xx" "ee" "hh" "aa" "pt" "p",
  let: "ch" := recv #() in
  bind: "ch'" := list_of_term (recv #()) in
  list_match: ["cr"; "offer"] := "ch'" in
  bind: "offer" := list_of_term "offer" in
  list_match: ["version"; "g"; "gx"; "hhh"; "aaa"; "m"] := "offer" in
  assert: eq_term "version" tls13 in
  let: "kdf_es_res" := kdf_es "psk" in
  let: "early_secret" := Fst "kdf_es_res" in
  let: "kb" := Snd "kdf_es_res" in
  let: "zoffer" := term_of_list [tls13; "g"; "gx"; "hhh"; "aaa"; zero] in
  assert: eq_term "m" (hmac "kb" (term_of_list ["cr"; "zoffer"])) in
  let: "kdf_k0_res" := kdf_k0 "early_secret" "ch" in
  let: "kc0" := Fst "kdf_k0_res" in
  let: "ems0" := Snd "kdf_k0_res" in
  (* insert serverSession0(cr,psk,offer,kc0,ems0); *)

  let: "sr" := mknonce #() in
  let: "dh_res" := dh_keygen "g" in
  let: "y" := Fst "dh_res" in
  let: "gy" := Snd "dh_res" in
  let: "mode" := term_of_list [tls13; "g"; "gy"; "hh"; "aa"; "pt"] in
  let: "sh" := term_of_list ["sr"; "mode"] in
  send "sh";;
  let: "log" := term_of_list ["ch"; "sh"] in
  (* get longTermKeys(sn,sk,p) *)
  (* event ServerChoosesVersion(cr,sr,p,TLS13); *)
  (* event ServerChoosesKEX(cr,sr,p,TLS13,DHE_13(g,gy)); *)
  (* event ServerChoosesAE(cr,sr,p,TLS13,a); *)
  (* event ServerChoosesHash(cr,sr,p,TLS13,h); *)

  let: "gxy" := texp "gx" "y" in
  let: "handshake_secret" := kdf_hs "early_secret" "gxy" in
  bind: "kdf_ms_res" := list_of_term (kdf_ms "handshake_secret" "log") in
  list_match: ["master_secret"; "chk"; "shk"; "cfin"; "sfin"] := "kdf_ms_res" in
  send (term_of_list ["chk"; "shk"]) ;;
  send "p";;
  let: "log" := term_of_list ["log"; "p"] in
  let: "sg" := sign "sg" "sk" (hash "hh" "log") in
  send "sg";;

  let: "log" := term_of_list ["log"; "sg"] in
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
