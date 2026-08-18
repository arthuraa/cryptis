From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term gmeta cryptis primitives tactics role.
From cryptis.examples Require Import iso_dh gen_conn.
From cryptis.examples.sess Require impl.
From cryptis.examples.sess.proofs Require Import base.
From cryptis.examples.sess Require Import proofs.
From actris.channel Require Import proto_model proto.

Ltac f_dist_le :=
  match goal with
  | H : _ ≡{?n}≡ _ |- _ ≡{?n'}≡ _ => apply (dist_le n); [apply H|lia]
  end.

Ltac solve_proto_contractive :=
  solve_proper_core ltac:(fun _ =>
    first [f_contractive; simpl in * | f_equiv | f_dist_le]).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Record handler := Handler {
  handler_tag : namespace;
  handler_val : val;
}.

Global Instance repr_handler : Repr handler := λ h,
  (λ: "t",
     bind: "t" := untag (Tag (handler_tag h)) "t" in
     SOME (handler_val h "t"))%V.

Section Tag.

Context `{!cryptisGS Σ, !heapGS Σ, !iso_dhGS Σ, !GenConn.connGS Σ, !sessG Σ}.
Notation iProp := (iProp Σ).

Implicit Types (cs : GenConn.state).
Implicit Types (skI skR : sign_key) (kS t : term).
Implicit Types (N : namespace).

Program Definition iMsg_tag_def (ms : gmap namespace (iMsg Σ term)) : iMsg Σ term :=
  IMsg (λ t, λne pp, ∃ N t' m,
          ⌜ms !! N = Some m ∧ t = Spec.tag (Tag N) t'⌝ ∗
          iMsg_car m t' pp)%I.
Next Obligation. solve_proper. Qed.
Definition iMsg_tag_aux : seal iMsg_tag_def.
Proof. by eexists. Qed.
Definition iMsg_tag := unseal iMsg_tag_aux.
Lemma iMsg_tag_unseal : iMsg_tag = iMsg_tag_def.
Proof. exact: seal_eq. Qed.

Lemma iMsg_tag_eq ms t pp :
  iMsg_car (iMsg_tag ms) t pp =
  (∃ N t' m,
     ⌜ms !! N = Some m ∧ t = Spec.tag (Tag N) t'⌝ ∗
     iMsg_car m t' pp)%I.
Proof. by rewrite iMsg_tag_unseal. Qed.

Definition iProto_tag (a : action) ms : iProto Σ term :=
  iProto_message a (iMsg_tag ms).

Lemma iMsg_tag_alt (ms : gmap namespace (iMsg Σ term)) v lp :
  iMsg_car (iMsg_tag ms) v lp ⊣⊢
  ∃ N t', ⌜v = Spec.tag (Tag N) t'⌝ ∗
          from_option (λ m, iMsg_car m t' lp) False%I (ms !! N).
Proof.
rewrite iMsg_tag_eq. iSplit.
- iDestruct 1 as (N t' m [HN ->]) "Hm".
  iExists N, t'. rewrite HN /=. by iFrame.
- iDestruct 1 as (N t') "[-> Hm]".
  case E: (ms !! N) => [m|] /=; last by iDestruct "Hm" as "[]".
  iExists N, t', m. iFrame. by iPureIntro.
Qed.

Global Instance iMsg_tag_ne : NonExpansive iMsg_tag.
Proof.
move=> n ms1 ms2 Hms v lp.
rewrite !iMsg_tag_alt.
apply bi.exist_ne => N. apply bi.exist_ne => t'.
f_equiv.
move: (Hms N).
case: (ms1 !! N) => [m1|]; case: (ms2 !! N) => [m2|] //= Hm.
- inversion Hm as [?? Hm'|]; subst.
  by apply: iMsg_car_ne.
- by inversion Hm.
- by inversion Hm.
Qed.

Lemma iMsg_tag_proper :
  Proper ((≡) ==> (≡)) iMsg_tag.
Proof.
rewrite iMsg_tag_unseal.
intros ms1 ms2 Hms v lp; simpl. iSplit.
- iDestruct 1 as (N t' m0 [HN ->]) "Hm".
  move: (Hms N); rewrite HN.
  case E: (ms2 !! N) => [m2|] Hopt; last by inversion Hopt.
  inversion Hopt as [?? He|]; subst.
  iExists N, t', m2.
  iSplit; first by iPureIntro.
  iApply (bi.equiv_entails_1_1 _ _ (He t' lp)). iExact "Hm".
- iDestruct 1 as (N t' m0 [HN ->]) "Hm".
  move: (Hms N); rewrite HN.
  case E: (ms1 !! N) => [m2|] Hopt; last by inversion Hopt.
  inversion Hopt as [?? He|]; subst.
  iExists N, t', m2.
  iSplit; first by iPureIntro.
  iApply (bi.equiv_entails_1_2 _ _ (He t' lp)). iExact "Hm".
Qed.

Lemma iMsg_map_tag (f : iProto Σ term → iProto Σ term)
    (ms : gmap namespace (iMsg Σ term)) :
  iMsg_map f (iMsg_tag ms) ≡ iMsg_tag ((λ m, iMsg_map f m) <$> ms).
Proof.
rewrite iMsg_tag_unseal. intros v lp; simpl. iSplit.
- iDestruct 1 as (p1) "[H Heq]".
  iDestruct "H" as (N t' m0 [HN ->]) "Hm".
  iExists N, t', (iMsg_map f m0).
  iSplit; first by iPureIntro; rewrite lookup_fmap HN.
  simpl. iExists p1. iFrame.
- iDestruct 1 as (N t' m0 [HN ->]) "Hm".
  move: HN; rewrite lookup_fmap.
  case E: (ms !! N) => [m1|] //= => -[<-].
  iDestruct "Hm" as (p1) "[Hm Heq]".
  iExists p1. iFrame "Heq".
  iExists N, t', m1. iFrame. by iPureIntro.
Qed.

Lemma iMsg_dual_tag (ms : gmap namespace (iMsg Σ term)) :
  iMsg_dual (iMsg_tag ms) ≡ iMsg_tag (iMsg_dual <$> ms).
Proof. apply iMsg_map_tag. Qed.

Lemma iMsg_app_tag (ms : gmap namespace (iMsg Σ term)) (q : iProto Σ term) :
  (iMsg_tag ms <++> q)%msg ≡ iMsg_tag ((λ m, (m <++> q)%msg) <$> ms).
Proof. apply iMsg_map_tag. Qed.

Lemma iProto_dual_tag (a : action) (ms : gmap namespace (iMsg Σ term)) :
  iProto_dual (iProto_tag a ms)
  ≡ iProto_tag (action_dual a) (iMsg_dual <$> ms).
Proof. by rewrite /iProto_tag iProto_dual_message iMsg_dual_tag. Qed.

Lemma iProto_app_tag (a : action) (ms : gmap namespace (iMsg Σ term))
    (q : iProto Σ term) :
  (iProto_tag a ms <++> q)%proto
  ≡ iProto_tag a ((λ m, (m <++> q)%msg) <$> ms).
Proof. by rewrite /iProto_tag iProto_app_message iMsg_app_tag. Qed.

Lemma iMsg_tag_intro (ms : gmap namespace (iMsg Σ term)) N m t' pp :
  ms !! N = Some m →
  iMsg_car m t' pp -∗ iMsg_car (iMsg_tag ms) (Spec.tag (Tag N) t') pp.
Proof.
move=> HN. rewrite iMsg_tag_eq. iIntros "H".
iExists N, t', m. iFrame. by iPureIntro.
Qed.

Lemma wp_send_tag {TT : tele} skI skR rl cs
    (ms : gmap namespace (iMsg Σ term)) N
    (t : TT → term) (P : TT → iProp) (p : TT → iProto Σ term) (x : TT) :
  ms !! N = Some (∃.. y, MSG t y {{ P y }}; p y)%msg →
  {{{ connected skI skR rl cs (iProto_tag Send ms) ∗
      public (t x) ∗
      (public (si_key cs) ∨ P x) }}}
    impl.send (repr cs) (Spec.tag (Tag N) (t x))
  {{{ RET #(); connected skI skR rl cs (p x) }}}.
Proof.
move=> HN. iIntros (Φ) "(conn & #p_t & Hdisj) post".
iApply (wp_send_msg _ _ _ _ (iMsg_tag ms) _ (p x) with "[conn Hdisj] post").
iSplitL "conn"; first by rewrite /iProto_tag.
iSplitR; first by rewrite public_tag.
iDestruct "Hdisj" as "[#fail|HP]"; first by iLeft.
iRight. iApply (iMsg_tag_intro _ _ HN).
rewrite iMsg_texist_exist bi_texist_exist. iExists x.
rewrite iMsg_base_eq /=.
iSplit; first done.
iFrame "HP".
auto.
Qed.

Lemma wp_handle N f φ :
  (∀ h, ⌜h = Handler N f⌝ -∗ φ (repr h)) -∗
  WP impl.handle (Tag N) f {{ φ }}.
Proof.
iIntros "post"; wp_lam; wp_pures.
by iApply ("post" $! (Handler N f)).
Qed.

Definition select_vc skI skR rl cs
    (ms : gmap namespace (iMsg Σ term)) (handlers : list handler) φ : iProp :=
  [∧ list] h ∈ handlers,
    ∀ (t : term) p,
      connected skI skR rl cs p -∗
      public t -∗
      public (si_key cs) ∨
        match ms !! handler_tag h with
        | Some m => iMsg_car m t (Next p)
        | None => False
        end -∗
       WP handler_val h t {{ v, φ (SOMEV v) }}.

Lemma wp_select skI skR rl cs ms (handlers : list handler) (V : iProp) φ :
  dom ms ⊆ list_to_set (map handler_tag handlers) →
  connected skI skR rl cs (<?> iMsg_tag ms) -∗
  V -∗
  (V -∗ select_vc skI skR rl cs ms handlers φ) -∗
  (∀ p, connected skI skR rl cs p -∗ public (si_key cs) -∗ V -∗ φ NONEV) -∗
  WP impl.select (repr cs) (repr handlers) {{ φ }}.
Proof.
iIntros "%sub conn V vc fail"; wp_lam; wp_pures.
wp_apply (wp_recv with "conn").
iIntros (t p) "(#p_t & conn & t_p)"; wp_pures.
pose (I := (λ hs : list handler,
  ⌜∀ h, h ∈ hs → h ∈ handlers⌝ ∗
  (public (si_key cs) ∨
     ∃ N t', ⌜t = Spec.tag (Tag N) t'⌝ ∗
             ⌜N ∈ map handler_tag hs⌝ ∗
             match ms !! N with
             | Some m => iMsg_car m t' (Next p)
             | None => False
             end) ∗
  connected skI skR rl cs p ∗
  V ∗
  (V -∗ select_vc skI skR rl cs ms handlers φ))%I).
iApply (wp_scan_list' I φ with "[] [fail] [vc conn t_p V]").
- iIntros "!> %h %hs %ξ !> (%mem & t_p & conn & V & vc) post".
  wp_pures; wp_lam; wp_apply wp_untag.
  case: Spec.untagP => [ {}t ->|ne] in I *; wp_pures.
  { iPoseProof ("vc" with "V") as "vc".
    have h_in : h ∈ handlers by apply: mem; apply: elem_of_list_here.
    rewrite /select_vc.
    iDestruct (big_andL_elem_of _ _ _ h_in with "vc") as "wp".
    wp_bind (handler_val h t).
    iAssert (public t) as "#p_t'"; first by iApply public_tag.
    iApply (wp_wand with "[t_p conn wp]").
    - iApply ("wp" with "[$] [//]").
      iDestruct "t_p" as "[#fail|(%N & %t' & %HN & _ & t_p)]"; eauto.
      by case/Spec.tag_inj: HN => /Tag_inj <- <- {t'}; eauto.
    - by iIntros "%v φ_v"; wp_pures; iApply ("post" $! (Some v)). }
  iApply ("post" $! None); iModIntro.
  iSplitR.
  { iPureIntro => h' h'_in. apply: mem. by apply: elem_of_list_further. }
  iSplitL "t_p".
  { iDestruct "t_p" as "[#fail|(%N & %t' & %et & %HN & t_p)]"; eauto.
    rewrite /= elem_of_cons in HN.
    case: HN => [->|HN] in et *; first by case: (ne _ et).
    by iRight; iExists N, t'; eauto. }
  by iFrame.
- iIntros "(%mem & t_p & conn & V & vc)".
  iDestruct "t_p" as "[#fail'|(%N & %t' & _ & %contra & _)]";
    last by rewrite /= elem_of_nil in contra.
  iApply ("fail" with "conn fail' V").
- iSplitR; first by iPureIntro.
  iSplitL "t_p".
  { iDestruct "t_p" as "[#fail|t_p]"; first by eauto.
    rewrite iMsg_tag_eq; iDestruct "t_p" as "(%N & %t' & %m & %em & t_p)".
    case: em => ms_N ->; iRight; iExists N, t'; rewrite ms_N; iFrame.
    iSplit; eauto; iPureIntro.
    have /sub: N ∈ dom ms by rewrite elem_of_dom ms_N.
    by rewrite elem_of_list_to_set. }
  by iFrame.
Qed.

End Tag.
