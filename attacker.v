From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl namespace_map frac.
From iris.base_logic.lib Require Import auth.
From iris.heap_lang Require Import notation proofmode metatheory.
From iris.heap_lang.lib Require Import lock ticket_lock.
From crypto Require Import lib term crypto primitives tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Attacker.

Context `{!cryptoG Σ, !heapG Σ, !tlockG Σ}.
Notation iProp := (iProp Σ).

Implicit Types (v : val) (t : term) (e : expr).
Implicit Types (T S : val → iProp).

Inductive type :=
| Pub
| EK
| DK
| Int
| Bool
| Unit
| Ref of type
| Prod of type & type
| Sum  of type & type
| List of type
| Arrow of type & type.

Implicit Types (Γ : gmap string type) (τ σ : type).
Implicit Types (vs : gmap string val).

Definition Option τ := Sum Unit τ.

Definition pub_type v : iProp :=
  ∃ t, ⌜v = t⌝ ∧ pterm t.

Definition ek_type v : iProp :=
  ∃ k, ⌜v = TKey Enc k⌝ ∧ pterm (TKey Enc k).

Definition dk_type v : iProp :=
  ∃ k, ⌜v = TKey Dec k⌝ ∧ pterm (TKey Dec k).

Definition int_type v : iProp :=
  ∃ n : Z, ⌜v = #n⌝.

Definition bool_type v : iProp :=
  ∃ b : bool, ⌜v = #b⌝.

Definition unit_type v : iProp :=
  ⌜v = #()⌝.

Definition ref_type T v : iProp :=
  ∃ l : loc, ⌜v = #l⌝ ∧ inv cryptisN (∃ v', l ↦ v' ∧ T v').

Definition prod_type T S v : iProp :=
  ∃ v₁ v₂, ⌜v = (v₁, v₂)%V⌝ ∧ T v₁ ∧ S v₂.

Definition sum_type T S v : iProp :=
  (∃ v', ⌜v = InjLV v'⌝ ∧ T v') ∨
  (∃ v', ⌜v = InjRV v'⌝ ∧ S v').

Definition list_type T v : iProp :=
  ∃ vs : list val, ⌜v = repr vs⌝ ∧
                   [∗ list] v' ∈ vs, T v'.

Definition arrow_type T S v : iProp :=
  □ ∀ v₁, T v₁ → WP v v₁ {{ S }}.

Reserved Notation "⟦ x ⟧ᵥ" (at level 0, format "⟦ x ⟧ᵥ").

Fixpoint type_den τ : val → iProp :=
  match τ with
  | Pub => pub_type
  | EK => ek_type
  | DK => dk_type
  | Int => int_type
  | Bool => bool_type
  | Unit => unit_type
  | Ref τ => ref_type ⟦τ⟧ᵥ
  | Prod τ σ => prod_type ⟦τ⟧ᵥ ⟦σ⟧ᵥ
  | Sum τ σ => sum_type ⟦τ⟧ᵥ ⟦σ⟧ᵥ
  | List τ => list_type ⟦τ⟧ᵥ
  | Arrow τ σ => arrow_type ⟦τ⟧ᵥ ⟦σ⟧ᵥ
  end
  where "⟦ x ⟧ᵥ" := (type_den x).

Global Instance type_den_persistent τ v : Persistent (⟦τ⟧ᵥ v).
Proof. by elim: τ v =>> /=; apply _. Qed.

Definition env_den Γ vs : iProp :=
  ∃ Γvs, ⌜Γ = fst <$> Γvs⌝ ∧ ⌜vs = snd <$> Γvs⌝ ∧
  [∗ map] τv ∈ Γvs, ⟦τv.1⟧ᵥ τv.2.

Notation "⟦ Γ ⟧*" := (env_den Γ) (at level 0, format "⟦ Γ ⟧*").

Global Instance env_den_persistent Γ vs : Persistent (⟦Γ⟧* vs).
Proof. by apply _. Qed.

Lemma env_den_delete Γ vs x :
  ⟦Γ⟧* vs -∗
  ⟦binder_delete x Γ⟧* (binder_delete x vs).
Proof.
iDestruct 1 as (Γvs) "(-> & -> & #H)".
iExists (binder_delete x Γvs).
rewrite !fmap_binder_delete; do !iSplit => //.
case: x => [|x] //=.
destruct (Γvs !! x) as [τv|] eqn:Γvs_x.
- by rewrite big_sepM_delete //; iDestruct "H" as "[_ ?]".
- by rewrite delete_notin.
Qed.

Lemma env_den_insert Γ vs τ v i :
  ⟦τ⟧ᵥ v -∗
  ⟦Γ⟧* vs -∗
  ⟦binder_insert i τ Γ⟧* (binder_insert i v vs).
Proof.
iIntros "#vP"; iDestruct 1 as (Γvs) "(-> & -> & #H)".
iExists (binder_insert i (τ, v) Γvs).
rewrite !fmap_binder_insert /=; do !iSplit => //.
case: i => [|i] //=.
destruct (Γvs !! i) as [τv|] eqn:Γvs_i.
- rewrite big_sepM_delete //; iDestruct "H" as "[_ H]".
  by rewrite big_sepM_insert_delete; eauto.
- by rewrite big_sepM_insert; eauto.
Qed.

Definition has_type Γ e τ : iProp :=
  □ ∀ γ, ⟦Γ⟧* γ → WP subst_map γ e {{ ⟦τ⟧ᵥ }}.

Lemma pub_typeI t : pterm t -∗ pub_type t.
Proof. iIntros "?"; iExists _; eauto. Qed.

Lemma int_typeI (n : Z) : ⊢ int_type #n.
Proof. iExists _; eauto. Qed.

Lemma bool_typeI (b : bool) : ⊢ bool_type #b.
Proof. iExists _; eauto. Qed.

Lemma unit_typeI : ⊢ unit_type #().
Proof. eauto. Qed.

Lemma sum_typeIL T S v : T v -∗ sum_type T S (InjLV v).
Proof. by iIntros "?"; iLeft; iExists _; eauto. Qed.

Lemma sum_typeIR T S v : S v -∗ sum_type T S (InjRV v).
Proof. by iIntros "?"; iRight; iExists _; eauto. Qed.

Lemma has_type_var Γ (x : string) τ :
  Γ !! x = Some τ →
  ⊢ has_type Γ x τ.
Proof.
iIntros "%Γ_x !> %vs".
iDestruct 1 as (Γvs) "(-> & -> & #vsP)".
rewrite lookup_fmap in Γ_x.
case Γvs_x: (Γvs !! _) Γ_x => [τv|] //= [<-].
rewrite lookup_fmap Γvs_x /=.
rewrite big_sepM_delete //; iDestruct "vsP" as "[vP _]".
by wp_finish.
Qed.

Lemma has_type_val Γ v τ : ⟦τ⟧ᵥ v -∗ has_type Γ v τ.
Proof. by iIntros "#vP !> %vs #vsP"; wp_finish. Qed.

Lemma has_type_tint Γ e :
  has_type Γ e Int -∗
  has_type Γ (tint e) Pub.
Proof.
rewrite /has_type /=.
iIntros "#eP !> %vs #vsP".
wp_bind (subst_map _ e); iApply wp_wand; first by iApply "eP".
iIntros (?); iDestruct 1 as (n) "->".
iApply wp_tint; iExists _; iSplit; eauto.
by rewrite pterm_TInt.
Qed.

Lemma has_type_as_int Γ e :
  has_type Γ e Pub -∗
  has_type Γ (to_int e) (Option Int).
Proof.
rewrite /has_type /=.
iIntros "#eP !> %vs #vsP".
wp_bind (subst_map _ _); iApply wp_wand; first by iApply "eP".
iIntros (?); iDestruct 1 as (t) "[-> #tP]".
iApply wp_to_int; case: Spec.to_intP => [n ->|?] //=.
- by iApply sum_typeIR; iApply int_typeI.
- by iApply sum_typeIL; iApply unit_typeI.
Qed.

Lemma has_type_app Γ e1 e2 τ σ :
  has_type Γ e2 τ -∗
  has_type Γ e1 (Arrow τ σ) -∗
  has_type Γ (e1 e2) σ.
Proof.
rewrite /has_type /=.
iIntros "#e2P #e1P !> %vs #vsP".
iSpecialize ("e1P" with "vsP").
iSpecialize ("e2P" with "vsP").
wp_bind (subst_map _ e2); iApply wp_wand; first by iApply "e2P".
iIntros "%v2 #v2P".
wp_bind (subst_map _ e1); iApply wp_wand; first by iApply "e1P".
iIntros "%v1 #v1P"; iSpecialize ("v1P" with "v2P").
wp_pures; by iApply "v1P".
Qed.

Lemma has_type_rec Γ f x τ e σ :
  has_type (binder_insert f (Arrow τ σ) (binder_insert x τ Γ)) e σ -∗
  has_type Γ (Rec f x e) (Arrow τ σ).
Proof.
rewrite /has_type /=.
iIntros "#eP !> %vs #vsP".
rewrite binder_delete_commute -(binder_insert_delete2 Γ).
rewrite (env_den_delete _ _ x) (env_den_delete _ _ f).
move eΓ': (binder_delete f _) => Γ'.
move evs': (binder_delete f _) => vs'.
iAssert (∀ v1, ⟦Arrow τ σ⟧ᵥ v1 -∗ ∀ v2, ⟦τ⟧ᵥ v2 -∗
         WP subst_map (binder_insert f v1 (binder_insert x v2 vs')) e {{ ⟦σ⟧ᵥ }})%I
        as "{eP vsP} eP".
  iIntros "%v1 #v1P %v2 #v2P".
  iApply "eP" => //.
  by do 2!iApply env_den_insert => //.
wp_pures.
iLöb as "IH"; iIntros "!> %v1 #v1P"; wp_pures.
rewrite /= -{4}evs' binder_delete_commute  -subst_map_binder_insert_2.
rewrite -(binder_insert_delete2 vs) evs'.
by iApply "eP".
Qed.

Lemma has_type_mknonce Γ e :
  ⊢ has_type Γ (mknonce #()) Pub.
Proof.
iIntros "!> %γ #γP /=".
iApply (wp_mknonce _ True%I (λ _, True)%I).
iIntros (t) "_ #tP _ _".
iExists t; iSplit => //.
by iApply "tP".
Qed.

Lemma has_type_mkkey Γ e :
  has_type Γ e Pub -∗
  has_type Γ (mkkey e) (Prod EK DK).
Proof.
iIntros "#eP !> %γ #γP /=".
wp_bind (subst_map _ _); iApply wp_wand; first by iApply "eP".
iIntros "%"; iDestruct 1 as (t) "[-> #tP]".
iApply wp_mkkey; iExists _, _; do 2!iSplit => //=.
- iExists _; iSplit => //; rewrite pterm_TKey; eauto.
- iExists _; iSplit => //; rewrite pterm_TKey; eauto.
Qed.

Lemma has_type_to_ek Γ e :
  has_type Γ e Pub -∗
  has_type Γ (to_ek e) (Option EK).
Proof.
iIntros "eP"; iApply (has_type_app with "eP").
iApply has_type_val.
rewrite /to_ek /=.
iIntros "!>"; iDestruct 1 as (t) "[-> #tP]".
wp_pures; wp_bind (is_key _); iApply wp_is_key.
case: Spec.is_keyP => [[|] k ->|_]; wp_pures.
- iApply sum_typeIR; iExists _; eauto.
- iApply sum_typeIL; iApply unit_typeI.
- iApply sum_typeIL; iApply unit_typeI.
Qed.

Lemma has_type_to_dk Γ e :
  has_type Γ e Pub -∗
  has_type Γ (to_dk e) (Option DK).
Proof.
iIntros "eP"; iApply (has_type_app with "eP").
iApply has_type_val.
rewrite /to_dk /=.
iIntros "!>"; iDestruct 1 as (t) "[-> #tP]".
wp_pures; wp_bind (is_key _); iApply wp_is_key.
case: Spec.is_keyP => [[|] k ->|_]; wp_pures.
- iApply sum_typeIL; iApply unit_typeI.
- iApply sum_typeIR; iExists _; eauto.
- iApply sum_typeIL; iApply unit_typeI.
Qed.

Lemma has_type_mono Γ e τ σ :
  (∀ v, ⟦τ⟧ᵥ v -∗ ⟦σ⟧ᵥ v) →
  has_type Γ e τ -∗
  has_type Γ e σ.
Proof.
iIntros "%sub #eP %vs !> #vsP".
iApply wp_wand; first iApply "eP" => //.
by iIntros (v) "#vP"; iApply sub.
Qed.

Lemma has_type_of_ek Γ e : has_type Γ e EK -∗ has_type Γ e Pub.
Proof.
apply: has_type_mono => v.
iDestruct 1 as (k) "[-> #H]".
by iExists _; eauto.
Qed.

Lemma has_type_of_dk Γ e : has_type Γ e DK -∗ has_type Γ e Pub.
Proof.
apply: has_type_mono => v.
iDestruct 1 as (k) "[-> #H]".
by iExists _; eauto.
Qed.

Lemma has_type_eq_term Γ e1 e2 :
  has_type Γ e1 Pub -∗
  has_type Γ e2 Pub -∗
  has_type Γ (eq_term e1 e2) Bool.
Proof.
iIntros "#e1P #e2P !> %vs #vsP /=".
wp_bind (subst_map _ e2); iApply wp_wand; first iApply "e2P" => //.
iIntros "%v2"; iDestruct 1 as (t2) "[-> _]".
wp_bind (subst_map _ e1); iApply wp_wand; first iApply "e1P" => //.
iIntros "%v1"; iDestruct 1 as (t1) "[-> _]".
iApply wp_eq_term; iApply bool_typeI.
Qed.

Lemma has_type_tgroup Γ e :
  has_type Γ e Pub -∗
  has_type Γ (tgroup e) Pub.
Proof.
iIntros "#eP !> %vs #vsP /=".
wp_bind (subst_map _ e); iApply wp_wand; first iApply "eP" => //.
iIntros "%"; iDestruct 1 as (t) "[-> #tP]".
iApply wp_tgroup; iExists _; iSplit => //.
by rewrite pterm_TExp0 -pterm_sterm.
Qed.

Lemma has_type_texp Γ e1 e2 :
  has_type Γ e1 Pub -∗
  has_type Γ e2 Pub -∗
  has_type Γ (texp e1 e2) Pub.
Proof.
iIntros "#e1P #e2P !> %vs #vsP /=".
wp_bind (subst_map _ e2); iApply wp_wand; first iApply "e2P" => //.
iIntros "%v2"; iDestruct 1 as (t2) "[-> #t2P]".
wp_bind (subst_map _ e1); iApply wp_wand; first iApply "e1P" => //.
iIntros "%v1"; iDestruct 1 as (t1) "[-> #t1P]".
iApply wp_texp; iExists _; iSplit => //.
by iApply pterm_texp.
Qed.

Lemma has_type_hash Γ e :
  has_type Γ e Pub -∗
  has_type Γ (hash e) Pub.
Proof.
iIntros "#eP !> %vs #vsP /=".
wp_bind (subst_map _ e); iApply wp_wand; first iApply "eP" => //.
iIntros "%"; iDestruct 1 as (t) "[-> #tP]".
iApply wp_hash; iExists _; iSplit => //.
by rewrite pterm_THash; iLeft.
Qed.

Lemma has_type_enc Γ e1 e2 :
  has_type Γ e1 EK -∗
  has_type Γ e2 Pub -∗
  has_type Γ (enc e1 e2) Pub.
Proof.
iIntros "#e1P #e2P !> %vs #vsP /=".
wp_bind (subst_map _ e2); iApply wp_wand; first iApply "e2P" => //.
iIntros "%v2"; iDestruct 1 as (t2) "[-> #t2P]".
wp_bind (subst_map _ e1); iApply wp_wand; first iApply "e1P" => //.
iIntros "%v1"; iDestruct 1 as (t1) "[-> #t1P]".
iApply wp_enc; iExists _; iSplit => //=.
by rewrite pterm_TEnc; eauto.
Qed.

Lemma has_type_dec Γ e1 e2 :
  has_type Γ e1 DK -∗
  has_type Γ e2 Pub -∗
  has_type Γ (dec e1 e2) (Option Pub).
Proof.
iIntros "#e1P #e2P !> %vs #vsP /=".
wp_bind (subst_map _ e2); iApply wp_wand; first iApply "e2P" => //.
iIntros "%v2"; iDestruct 1 as (t2) "[-> #t2P]".
wp_bind (subst_map _ e1); iApply wp_wand; first iApply "e1P" => //.
iIntros "%v1"; iDestruct 1 as (t1) "[-> #t1P]".
iApply wp_dec => /=.
case: t2; try by move => *; iApply sum_typeIL.
move=> t1' t2'.
case: decide => [->|?]; last by iApply sum_typeIL.
iApply sum_typeIR; iApply pub_typeI.
rewrite [pterm (TEnc _ _)]pterm_TEnc.
iDestruct "t2P" as "[[_ ?]|(_ & _ & #t2P)]" => //.
by iApply "t2P".
Qed.

Lemma has_type_tag Γ c e :
  has_type Γ e Pub -∗
  has_type Γ (tag c e) Pub.
Proof.
iIntros "#eP !> %vs #vsP /=".
wp_bind (subst_map _ e); iApply wp_wand; first iApply "eP" => //.
iIntros "%"; iDestruct 1 as (t) "[-> #tP]".
iApply wp_tag; iApply pub_typeI.
by rewrite pterm_tag.
Qed.

Lemma has_type_untag Γ c e :
  has_type Γ e Pub -∗
  has_type Γ (untag c e) (Option Pub).
Proof.
iIntros "#eP !> %vs #vsP /=".
wp_bind (subst_map _ e); iApply wp_wand; first iApply "eP" => //.
iIntros "%"; iDestruct 1 as (t) "[-> #tP]".
iApply wp_untag.
case: Spec.untagP => [t' ->|_] /=.
- iApply sum_typeIR. iApply pub_typeI. by rewrite pterm_tag.
- by iApply sum_typeIL.
Qed.

Lemma list_pub_typeE v :
  ⟦List Pub⟧ᵥ v -∗
  ∃ ts : list term, ⌜v = repr ts⌝ ∗ [∗ list] t ∈ ts, pterm t.
Proof.
iDestruct 1 as (vs) "[-> #vsP]".
rewrite /= !repr_list_eq.
iInduction vs as [|v vs] "IH" => /=.
- by iExists []; iSplit => //.
- iDestruct "vsP" as "[vP vsP]".
  iDestruct ("IH" with "vsP") as (ts) "[-> tsP]".
  iDestruct "vP" as (t) "[-> tP]".
  by iExists (t :: ts); iSplit => //=; iSplit.
Qed.

Lemma has_type_term_of_list Γ e :
  has_type Γ e (List Pub) -∗
  has_type Γ (term_of_list e) Pub.
Proof.
iIntros "#eP !> %vs #vsP /=".
wp_bind (subst_map _ e); iApply wp_wand; first iApply "eP" => //.
iIntros "%v #vP".
iDestruct (list_pub_typeE with "vP") as (ts) "[-> #tsP]".
iApply wp_term_of_list; iApply pub_typeI.
by rewrite pterm_of_list.
Qed.

Lemma has_type_list_of_term Γ e :
  has_type Γ e Pub -∗
  has_type Γ (list_of_term e) (Option (List Pub)).
Proof.
iIntros "#eP !> %vs #vsP /=".
wp_bind (subst_map _ e); iApply wp_wand; first iApply "eP" => //.
iIntros "%v #vP"; iDestruct "vP" as (t) "[-> tP]".
iApply wp_list_of_term.
case: Spec.to_listP => [ts|?] /=; last by iApply sum_typeIL.
iApply sum_typeIR; iExists (map repr ts); rewrite /= -repr_list_val.
iSplit => //; rewrite pterm_of_list.
iInduction ts as [|t' ts] "IH" => //=.
iDestruct "tP" as "[tP tsP]"; iSplit; first by iApply pub_typeI.
by iApply "IH".
Qed.

Lemma has_type_nil Γ τ : ⊢ has_type Γ []%E (List τ).
Proof.
iIntros "!> %vs #vsP /=".
wp_pures.
by iExists []; rewrite repr_list_eq; eauto.
Qed.

Lemma has_type_cons Γ e1 e2 τ :
  has_type Γ e1 τ -∗
  has_type Γ e2 (List τ) -∗
  has_type Γ (e1 :: e2) (List τ).
Proof.
iIntros "#e1P #e2P !> %vs #vsP /=".
wp_bind (subst_map _ e2); iApply wp_wand; first iApply "e2P" => //.
iIntros "%v2"; iDestruct 1 as (vs') "[-> #t2P]".
wp_bind (subst_map _ e1); iApply wp_wand; first iApply "e1P" => //.
iIntros "%v1 #v1P"; rewrite /CONS; wp_pures.
iExists (v1 :: vs'); iSplit; rewrite /= ?repr_list_eq //.
by iSplit => //.
Qed.

Definition list_case : val := λ: "l" "f" "g",
  match: "l" with
    NONE => "f" #()
  | SOME "x" => "g" (Fst "x") (Snd "x")
  end.

Lemma has_type_list_case Γ e e1 e2 τ σ :
  has_type Γ e (List τ) -∗
  has_type Γ e1 (Arrow Unit σ) -∗
  has_type Γ e2 (Arrow τ (Arrow (List τ) σ)) -∗
  has_type Γ (list_case e e1 e2) σ.
Proof.
iIntros "#eP #e1P #e2P !> %vs #vsP /=".
wp_bind (subst_map _ e2); iApply wp_wand; first iApply "e2P" => //.
iIntros "%g #gP".
wp_bind (subst_map _ e1); iApply wp_wand; first iApply "e1P" => //.
iIntros "%f #fP".
wp_bind (subst_map _ e); iApply wp_wand; first iApply "eP" => //.
iIntros "%v"; iDestruct 1 as (l) "[-> #lP]".
case: l => [|x l] /=.
- rewrite repr_list_eq /= /list_case; wp_pures.
  by iApply "fP" => //.
- rewrite repr_list_eq /= /= -repr_list_eq /list_case; wp_pures.
  iDestruct "lP" as "[xP lP]".
  wp_bind (g x); iApply wp_wand; first iApply "gP" => //.
  iIntros "%g' #gP'".
  iApply "gP'" => //.
  by iExists l; iSplit => //.
Qed.

Lemma has_type_ref Γ e τ :
  has_type Γ e τ -∗
  has_type Γ (ref e) (Ref τ).
Proof.
iIntros "#eP !> %γ #γP /=".
wp_bind (subst_map _ _); iApply wp_wand; first by iApply "eP".
iIntros "%v #vP".
iApply wp_fupd.
wp_alloc l as "lP".
iMod (inv_alloc cryptisN _ (∃ v', l ↦ v' ∧ ⟦τ⟧ᵥ v') with "[lP]") as "#?"; eauto.
by iModIntro; iExists l; iSplit => //.
Qed.

Lemma has_type_get Γ e τ :
  has_type Γ e (Ref τ) -∗
  has_type Γ (!e) τ.
Proof.
iIntros "#eP !> %γ #γP /=".
wp_bind (subst_map _ _); iApply wp_wand; first by iApply "eP".
iIntros "%v"; iDestruct 1 as (l) "[-> #lP]".
iInv "lP" as (v') "[lP' #inv]"; wp_load.
by iModIntro; eauto.
Qed.

Lemma has_type_set Γ e1 e2 τ :
  has_type Γ e1 (Ref τ) -∗
  has_type Γ e2 τ -∗
  has_type Γ (e1 <- e2) Unit.
Proof.
iIntros "#e1P #e2P !> %γ #γP /=".
wp_bind (subst_map _ _); iApply wp_wand; first by iApply "e2P".
iIntros "%v #vP".
wp_bind (subst_map _ _); iApply wp_wand; first by iApply "e1P".
iIntros "%"; iDestruct 1 as (l) "[-> #lP]".
iInv "lP" as (v') "[lP' #inv]".
by wp_store; iModIntro; eauto.
Qed.

Lemma has_type_inl Γ e τ σ :
  has_type Γ e τ -∗
  has_type Γ (InjL e) (Sum τ σ).
Proof.
iIntros "#eP !> %γ #γP /=".
wp_bind (subst_map _ _); iApply wp_wand; first by iApply "eP".
iIntros "%v #vP".
by wp_pures; iApply sum_typeIL.
Qed.

Lemma has_type_inr Γ e τ σ :
  has_type Γ e σ -∗
  has_type Γ (InjR e) (Sum τ σ).
Proof.
iIntros "#eP !> %γ #γP /=".
wp_bind (subst_map _ _); iApply wp_wand; first by iApply "eP".
iIntros "%v #vP".
by wp_pures; iApply sum_typeIR.
Qed.

Lemma has_type_case Γ e e1 e2 τ₁ τ₂ σ :
  has_type Γ e (Sum τ₁ τ₂) -∗
  has_type Γ e1 (Arrow τ₁ σ) -∗
  has_type Γ e2 (Arrow τ₂ σ) -∗
  has_type Γ (Case e e1 e2) σ.
Proof.
iIntros "#eP #e1P #e2P !> %vs #vsP /=".
wp_bind (subst_map _ e); iApply wp_wand; first iApply "eP" => //.
iIntros "% #[vP|vP]"; iDestruct "vP" as (v) "[-> vP]"; wp_pures.
- wp_bind (subst_map _ _); iApply wp_wand; first by iApply "e1P".
  by iIntros "%f #fP"; iApply "fP".
- wp_bind (subst_map _ _); iApply wp_wand; first by iApply "e2P".
  by iIntros "%f #fP"; iApply "fP".
Qed.

Lemma has_type_pair Γ e1 e2 τ₁ τ₂ :
  has_type Γ e1 τ₁ -∗
  has_type Γ e2 τ₂ -∗
  has_type Γ (e1, e2) (Prod τ₁ τ₂).
Proof.
iIntros "#e1P #e2P !> %γ #γP /=".
wp_bind (subst_map _ _); iApply wp_wand; first by iApply "e2P".
iIntros "%v2 #v2P".
wp_bind (subst_map _ _); iApply wp_wand; first by iApply "e1P".
iIntros "%v1 #v1P".
by wp_pures; iExists _, _; eauto.
Qed.

Lemma has_type_fst Γ e τ σ :
  has_type Γ e (Prod τ σ) -∗
  has_type Γ (Fst e) τ.
Proof.
iIntros "#eP !> %γ #γP /=".
wp_bind (subst_map _ _); iApply wp_wand; first by iApply "eP".
iIntros "%"; iDestruct 1 as (v1 v2) "(-> & #? & #?)".
by wp_pures.
Qed.

Lemma has_type_snd Γ e τ σ :
  has_type Γ e (Prod τ σ) -∗
  has_type Γ (Snd e) σ.
Proof.
iIntros "#eP !> %γ #γP /=".
wp_bind (subst_map _ _); iApply wp_wand; first by iApply "eP".
iIntros "%"; iDestruct 1 as (v1 v2) "(-> & #? & #?)".
by wp_pures.
Qed.

Definition get_chan : val := λ: "c" "lock", rec: "loop" <> :=
  acquire "lock";;
  match: !"c" with
    NONE => release "lock";; "loop" #()
  | SOME "ts" => "c" <- Snd "ts";; release "lock";; Fst "ts"
  end.

Definition put_chan : val := λ: "c" "lock" "t",
  acquire "lock";;
  "c" <- SOME ("t", !"c");;
  release "lock".

Definition chan_inv (c : loc) : iProp :=
  ∃ ts : list term, c ↦ repr ts ∗ [∗ list] t ∈ ts, pterm t.

Definition mkchan : val := λ: <>,
  let: "c" := ref NONEV in
  let: "lock" := newlock #() in
  (get_chan "c" "lock", put_chan "c" "lock").

Lemma has_type_mkchan Γ :
  ⊢ has_type Γ mkchan (Arrow Unit (Prod (Arrow Unit Pub) (Arrow Pub Unit))).
Proof.
rewrite /mkchan; iApply has_type_val.
iIntros "!> %v _ "; wp_pures.
wp_alloc c as "cP"; wp_pures.
wp_bind (newlock _).
wp_pures; iApply (newlock_spec (chan_inv c) with "[cP]").
  iExists []; iSplit => //.
  by rewrite repr_list_eq.
iIntros "!> %lk %γ #lkP"; rewrite /get_chan /put_chan; wp_pures.
iExists _, _; do 2!iSplit => //.
- iLöb as "IH".
  iIntros "!> % _"; wp_pures.
  wp_bind (acquire _); iApply acquire_spec => //.
  iIntros "!> [locked inv]".
  iDestruct "inv" as (ts) "[c_ts #tsP]".
  wp_pures; wp_load; case: ts => [|t ts].
  + rewrite repr_list_eq /=; wp_pures.
    wp_bind (release _); iApply (release_spec with "[locked c_ts]").
      by iSplit => //; iFrame; iExists []; rewrite /= repr_list_eq /=; iFrame.
    iIntros "!> _"; wp_seq.
    by iApply "IH".
  + rewrite repr_list_eq /= -repr_list_eq.
    iDestruct "tsP" as "[tP tsP]".
    wp_pures; wp_store; wp_bind (release _).
    iApply (release_spec with "[locked c_ts]").
      by iSplit => //; iFrame; iExists ts; iFrame.
    by iIntros "!> _"; wp_pures; iApply pub_typeI.
- iIntros "!> %"; iDestruct 1 as (t) "[-> #tP]"; wp_pures.
  wp_bind (acquire _); iApply acquire_spec; eauto.
  iIntros "!> [locked cP]"; iDestruct "cP" as (ts) "[cP #tsP]".
  wp_pures; wp_load; wp_store.
  iApply (release_spec with "[locked cP]").
    iSplit => //; iFrame; iExists (t :: ts).
    by rewrite repr_list_eq; iFrame => //=; eauto.
  by [].
Qed.

End Attacker.
