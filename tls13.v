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

Section TLS13.

Context `{!heapG Σ, !cryptoG Σ, !network Σ}.
Notation iProp := (iProp Σ).

Implicit Types t : term.
Implicit Types s : session_view.
Implicit Types rl : role.

Variable N : namespace.

Definition hmac : val := λ: "k" "x",
  hash (term_of_list ["k"; "x"]).

Notation prf := hmac (only parsing).

Notation hkdf_extract := prf (only parsing).

Definition client_finished : term := TInt 0.
Definition server_finished : term := TInt 1.
Definition master_secret : term := TInt 2.
Definition client_key_expansion : term := TInt 3.
Definition server_key_expansion : term := TInt 4.
Definition tls13_client_handshake_traffic_secret : term := TInt 5.
Definition tls13_server_handshake_traffic_secret : term := TInt 6.
Definition tls13_client_early_traffic_secret : term := TInt 7.
Definition tls13_client_application_traffic_secret : term := TInt 8.
Definition tls13_server_application_traffic_secret : term := TInt 9.
Definition tls13_key : term := TInt 10.
Definition tls13_iv : term := TInt 11.
Definition tls13_early_exporter_master_secret : term := TInt 12.
Definition tls13_exporter_master_secret : term := TInt 13.
Definition tls13_resumption_master_secret : term := TInt 14.
Definition tls13_resumption_psk_binder_key : term := TInt 15.
Definition tls13_finished : term := TInt 16.

Definition zero : term := TInt 0.

Definition tls12 := TInt 2.
Definition tls13 := TInt 3.

Definition hkdf_expand_label : val := λ: "k" "l" "h",
  prf "k" (term_of_list ["l"; "h"]).

Definition derive_secret : val := λ: "k" "l" "m",
  hkdf_expand_label "k" "l" (hash "m").

Definition kdf_0 : val := λ: <>,
  hkdf_extract zero zero.

Definition kdf_es : val := λ: "psk",
  let: "es" := hkdf_extract zero "psk" in
  let: "kb" := derive_secret "es" tls13_resumption_psk_binder_key zero in
  term_of_list ["es"; "kb"].

Definition kdf_k0 : val := λ: "es" "log",
  let: "atsc0" :=
    derive_secret "es" tls13_client_early_traffic_secret "log" in
  let: "kc0"   :=
    hkdf_expand_label "atsc0" tls13_key zero in
  let: "ems0"  :=
    derive_secret "es" tls13_early_exporter_master_secret "log" in
  term_of_list ["kc0"; "ems0"].

Notation kdf_hs := hkdf_extract (only parsing).

Definition kdf_ms :val := λ: "hs" "log",
  let: "ms" := hkdf_extract "hs" zero in
  let: "htsc" :=
    derive_secret "hs" tls13_client_handshake_traffic_secret "log" in
  let: "htss" :=
    derive_secret "hs" tls13_server_handshake_traffic_secret "log" in
  let: "kch" :=  hkdf_expand_label "htsc" tls13_key zero in
  let: "kcm" :=  hkdf_expand_label "htsc" tls13_finished zero in
  let: "ksh" :=  hkdf_expand_label "htss" tls13_key zero in
  let: "ksm" :=  hkdf_expand_label "htss" tls13_finished zero in
  term_of_list ["ms"; "kch"; "ksh"; "kcm"; "ksm"].

Definition kdf_k : val := λ: "ms" "log",
  let: "atsc" :=
    derive_secret "ms" tls13_client_application_traffic_secret "log" in
  let: "atss" :=
    derive_secret "ms" tls13_server_application_traffic_secret "log" in
  let: "ems"  :=
    derive_secret "ms" tls13_exporter_master_secret "log" in
  let: "kc"   :=
    hkdf_expand_label "atsc" tls13_key zero in
  let: "ks"   :=
    hkdf_expand_label "atss" tls13_key zero in
  term_of_list ["kc"; "ks"; "ems"].

Definition kdf_psk : val := λ: "ms" "log",
  derive_secret "ms" tls13_resumption_master_secret "log".

Definition dh_keygen : val := λ: "g",
  let: "x" := mknonce #() in
  ("x", texp "g" "x").

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
