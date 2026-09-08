From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis Require Import role iso_dh conn.
From cryptis.examples Require Import iso_dh gen_conn.
From actris.channel Require Import proto.

From cryptis.examples.gen_conn.proofs Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation sessN := (nroot.@"sess").
Local Notation connN := (nroot.@"conn").

Module Impl.

Section Impl.

Definition connect : val := λ: "c" "skA" "pkB",
  let: "conn" := GenConn.connect "c" "skA" "pkB" in
  (#true, "conn").

Definition listen : val := λ: "c", GenConn.listen "c".

Definition confirm : val := λ: "c" "skB" "req",
  let: "conn" := GenConn.confirm "c" "skB" "req" in
  (#false, "conn").

Definition send : val := λ: "cs" "ts",
  let: "is_init" := Fst "cs" in
  let: "conn" := Snd "cs" in
  let: "N" := if: "is_init" then Tag (sessN.@"init") else
              Tag (sessN.@"resp") in
  GenConn.send "conn" "N" "ts".

Definition recv : val := λ: "cs",
  let: "is_init" := Fst "cs" in
  let: "conn" := Snd "cs" in
  let: "N" := if: "is_init" then Tag (sessN.@"resp") else
              Tag (sessN.@"init") in
  GenConn.recv "conn" "N".

End Impl.

End Impl.

Section Proofs.
  Notation iProto Σ := (iProto Σ term).
  Notation iMsg Σ := (iMsg Σ term).

  Record params Σ := Params {
  chan_inv :
    sign_key → sign_key → sess_info → list term → list term → iProp Σ;
  msg_inv :
    sign_key → sign_key → sess_info → role → term → iProp Σ;
                       }.

  Context `{!cryptisGS Σ, !heapGS Σ, !GenConn.connGS Σ, !protoG Σ term}.
  Notation iProp := (iProp Σ).

  Implicit Types (cs : GenConn.state).
  Implicit Types (kS t : term) (ts : list term).
  Implicit Types (skI skR : sign_key).
  Implicit Types n m : nat.
  Implicit Types b : bool.
  Implicit Types v : val.
  Implicit Types (ok : Prop) (failed : bool).
  Implicit Types (si : sess_info) (rl : role).
  (* Implicit Types (ps : params Σ). *)
  Implicit Types (p : iProto Σ).
  Implicit Types (N : namespace).

  (* Variable term_to_val : term → val. *)
  (* Variable val_to_term : val → term. *)
  Search term_meta.


Definition proto_msg_pred skI skR si rl t : iProp :=
  True.

Definition proto_chan_pred skI skR si rl t : iProp :=
  True.

  Definition iProto_pointsto
    N (rl : role) cs (p : iProto Σ) : iProp :=
    ∃ γ
      (* γr *)
      ,
        (* skI γl *)
        (if rl is Init then
          term_meta (si_init_share cs) N γ
          else term_meta (si_resp_share cs) N γ )
                         ∗
        (* term_meta γl N  *)
      (* chan_inv () ∗ *)
    iProto_own γ p.


Definition prot_connected N p ps skI skR rl cs : iProp :=
  connected ps skI skR rl cs ∗
            iProto_pointsto N rl cs p.
            (* ∗ *)
    (* ∃ γ, iProto_own γ prot. *)

Definition my_msg_inv `{!heapGS Σ}
    (p : iProto Σ) (skI skR : sign_key) (cs : sess_info) (rl : role) (t :term) : iProp  :=
    ∃ (p' : iProto Σ) (P : iProp Σ),
      (* let v := term_to_val t in *)
       iMsg_car (MSG (term_to_val t) {{P}}; p') \/ (Next p').


            Lemma wp_connect P p c skI skR :
  channel c -∗
  cryptis_ctx -∗
  ctx -∗
  minted skI -∗
  minted skR -∗
  {{{ GenConn.failure skI skR ∨ P }}}
    impl.connect c skI (Spec.pkey skR)
  {{{ cs, RET (repr cs);
      prot_connected N p skI skR Init cs ∗
      (compromised cs ∨ P) }}}.


Definition connected skI skR rl cs : iProp :=
  GenConn.connected {| GenConn.chan_inv := proto_chan_pred; GenConn.msg_inv := proto_chan_pred |}
    skI skR rl cs.

Definition proto_tokens cs : iProp :=
  True.
  (* public (si_key cs) ∨ *)
  (* resp_pred_token cs rpcN (TInt 0) ∗ *)
  (* resp_pred_token cs rpcN (TInt 0). *)


Definition proto_connected kI kR cs : iProp :=
  connected kI kR Init cs ∗
  release_token (si_init_share cs) ∗
  proto_tokens cs.

Lemma wp_connect P c skI skR :
  channel c -∗
  cryptis_ctx -∗
  ctx -∗
  minted skI -∗
  minted skR -∗
  {{{ GenConn.failure skI skR ∨ P }}}
    impl.connect c skI (Spec.pkey skR)
  {{{ cs, RET (repr cs);
      proto_connected skI skR cs ∗
      (compromised cs ∨ P) }}}.


Lemma wp_connect P c skI skR N ps :
  ctx N ps -∗
  {{{(failure skI skR ∨ P)}}}
    impl.connect c skI (Spec.pkey skR) (Tag N)
    {{{cs, RET (repr cs); True}}}.

Lemma my_wp_connect P c skI skR N ps :
  channel c ∗
  cryptis_ctx ∗
  ctx N ps ∗
  minted skI ∗
  minted skR -∗
  {{{ GenConn.failure skI skR ∨ P }}}
    impl.connect c skI (Spec.pkey skR) (Tag N)
  {{{ cs, RET (repr cs);
      connected ps skI skR Init cs ∗
      (public (si_key cs) ∨ P) ∗
      release_token (si_init_share cs) ∗
      term_token (si_init_share cs) (⊤ ∖ ↑iso_dhN ∖ ↑connN) }}}.
Proof. exact: GenConn.wp_connect. Qed.

(* Definition prot_pred N φ : iProp := *)
(*   True%I. *)
  (* nown iso_dh_name N *)
  (*   (saved_pred DfracDiscarded (λ '(skI, skR, si, rl), φ skI skR si rl)). *)
  Definition my_chan_inv `{!heapGS Σ, !protoG Σ term}
     N (skI skR : sign_key) (cs : sess_info) (tsI tsR : list term) : iProp :=
    ∃ ( yl yr : gname) , term_meta (si_init_share cs) N yl ∗ term_meta (si_resp_share cs) N yr ∗
                           iProto_ctx yl yr tsI tsR.

  Definition iProto_pointsto `{!heapGS Σ, !protoG Σ val}
    N (rl : role) cs (p : iProto Σ) : iProp :=
    ∃ γ
      (* γr *)
      ,
        (* skI γl *)
        (if rl is Init then
          term_meta (si_init_share cs) N γ
          else term_meta (si_resp_share cs) N γ )
                         ∗
        (* term_meta γl N  *)
      (* chan_inv () ∗ *)
    iProto_own γl p.


Definition prot_connected prot ps skI skR rl cs : iProp :=
  connected ps skI skR rl cs ∗
            iProto_pointsto (* rl *) prot
    ∃ γ, iProto_own γ prot.

Lemma wp_initiator P :
  Lemma wp_connect P prot_connected :

Lemma wp_initiator failed c skI skR N φ :
  channel c -∗
  cryptis_ctx -∗
  iso_dh_ctx -∗
  iso_dh_pred N φ -∗
  minted skI -∗
  minted skR -∗
  (if failed then public skI ∨ public skR else True) -∗
  {{{ True }}}
    initiator c skI (Spec.pkey skR) (Tag N)
  {{{ okS, RET (repr okS);
      if okS is Some kS then ∃ si,
        ⌜si_init si = skI⌝ ∗
        ⌜si_resp si = skR⌝ ∗
        ⌜si_key si = kS⌝ ∗
        minted kS ∗
        session si ∗
        □ (⌜failed⌝ → public (si_key si)) ∗
        release_token (si_init_share si) ∗
        term_token (si_init_share si) (⊤ ∖ ↑iso_dhN) ∗
        (public (si_key si) ∨ φ skI skR si Init)
      else True
 }}}.

Lemma wp_connect P c skI skR N ps :
  channel c ∗
  cryptis_ctx ∗
  ctx N ps ∗
  minted skI ∗
  minted skR -∗
  {{{ (failure skI skR ∨ P) }}}
    impl.connect c skI (Spec.pkey skR) (Tag N)
  {{{ cs, RET (repr cs);
      connected ps skI skR Init cs ∗
      (public (si_key cs) ∨ P) ∗
      release_token (si_init_share cs) ∗
      term_token (si_init_share cs) (⊤ ∖ ↑iso_dhN ∖ ↑connN) }}}.

  Definition my_chan_inv `{!heapGS Σ, !protoG Σ term}
     (skI skR : sign_key) (cs : sess_info) (tsI tsR : list term) : iProp :=
    (* let vsI := List.map term_to_val tsI in *)
    (* let vsR := List.map term_to_val tsR in *)

    ∃ ( yl yr : gname) , term_meta cs N yl ∗ term_meta cs N yr ∗
                           iProto_ctx yl yr tsI tsR.

  Definition iProto_pointsto `{!heapGS Σ, !protoG Σ val}
     (skI : sign_key) (p : iProto Σ) : iProp Σ :=
    iProto_own skI p.
  (* ∗ iProto_own yl pl ∗ iProto_own yr pr. *).

  Print iMsg_base.

  Definition my_msg_inv `{!heapGS Σ}
    (p : iProto Σ) (skI skR : sign_key) (cs : sess_info) (rl : role) (t :term) : iProp  :=
    ∃ (p' : iProto Σ) (P : iProp Σ),
      (* let v := term_to_val t in *)
       iMsg_car (MSG (term_to_val t) {{P}}; p') \/ (Next p').

(* Definition my_params {Σ} `{!heapGS Σ, !chanG Σ} (p : iProto Σ) : params Σ := *)
(*   Params (my_chan_inv p) (my_msg_inv p). *)

  Definition my_gen_params p : GenConn.params Σ := {|
    GenConn.chan_inv := my_chan_inv;
    GenConn.msg_inv := my_msg_inv p;
                                                  |}%I.


  Definition wp_initiator

  Definition iProto_pointsto_def `{!heapGS Σ}
    (cs : val) (p : iProto Σ) : iProp Σ :=
    ∃ cnts sess ch n,
      ∗


End Proofs.
