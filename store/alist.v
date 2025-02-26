From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import lock ticket_lock.
From cryptis Require Import lib term cryptis primitives tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module AList.

Definition empty : val := λ: <>, []%V.

Definition find : val := λ: "kvs" "k",
  let: "res" := find_list (λ: "kv", eq_term (Fst "kv") "k") "kvs" in
  match: "res" with
    SOME "res" => SOME (Snd "res")
  | NONE => NONE
  end.

Definition insert : val := λ: "kvs" "k" "v",
  ("k", "v") :: "kvs".

Definition delete : val := λ: "kvs" "k",
  filter_list (λ: "p", ~ eq_term "k" (Fst "p")) "kvs".

Section Verif.

Context `{!cryptisGS Σ, !heapGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (γ : gname) (l : loc) (k t : term) (v : val).
Implicit Types (kvs : list (term * val)) (db : gmap term val).

Definition is_alist v db : Prop :=
  ∃ kvs, v = repr kvs ∧
  ∀ k, db !! k = snd <$> List.find (λ p, bool_decide (p.1 = k)) kvs.

Lemma wp_empty E :
  {{{ True }}}
    empty #() @ E
  {{{ v, RET v; ⌜is_alist v ∅⌝ }}}.
Proof.
iIntros "%Φ _ Hpost". wp_lam. iApply "Hpost". iIntros "!>".
iPureIntro. exists []. rewrite /repr repr_list_unseal. split => //.
Qed.

Lemma wp_find E v db t :
  is_alist v db →
  {{{ True }}}
    find v t @ E
  {{{ RET (repr (db !! t)); True }}}.
Proof.
case=> [kvs] [-> {v}] kvs_db.
iIntros "%Φ _ Hpost"; wp_lam; wp_pures.
wp_bind (find_list _ _).
iApply (wp_find_list (λ x, bool_decide (x.1 = t)) _ kvs) => //.
{ move=> [k t']; iIntros "%Φ' _ Hpost".
  wp_pures. iApply wp_eq_term. by iApply "Hpost". }
iIntros "!> _"; rewrite kvs_db.
by case: List.find => [[k' t']|] /=; wp_pures; iApply "Hpost".
Qed.

Lemma wp_insert v db k v' E :
  is_alist v db ->
  {{{ True }}}
    insert v k v' @ E
  {{{ r, RET r; ⌜is_alist r (<[k := v']>db)⌝ }}}.
Proof.
case=> [kvs] [-> {v}] kvs_db. iIntros "%Φ _ Hpost".
wp_lam. wp_pures. iApply (wp_cons _ (k, v')). iApply "Hpost".
iPureIntro. exists ((k, v') :: kvs); split => //= k'.
case: bool_decide_reflect => [<-|ne] //=;
by rewrite (lookup_insert, lookup_insert_ne).
Qed.

Lemma wp_delete v db k E :
  is_alist v db →
  {{{ True }}}
    delete v k @ E
  {{{ v', RET v'; ⌜is_alist v' (base.delete k db)⌝ }}}.
Proof.
case=> [kvs] [-> {v}] kvs_db. iIntros "%Φ _ Hpost".
wp_lam; wp_pures.
iApply (wp_filter_list (λ p : term * val, negb (bool_decide (k = p.1))))
       => //.
{ iIntros "%p %Ψ _ Hpost". wp_pures. wp_bind (eq_term _ _).
  iApply wp_eq_term. wp_pures. by iApply "Hpost". }
iIntros "!> _". iApply "Hpost". iPureIntro.
eexists _; split; eauto => // k'. case: (decide (k = k')) => [<- {k'}|ne].
- rewrite lookup_delete. case eq_find: List.find => [[t1 t2]|] //=.
  case/(@find_some _ _ _ _): eq_find => /= in_filter.
  case: bool_decide_reflect => // -> in in_filter *.
  rewrite filter_In /= in in_filter; case: in_filter => _.
  by rewrite bool_decide_eq_true_2.
- rewrite lookup_delete_ne // {}kvs_db.
  elim: kvs => //= - [/= t1 t2] kvs IH.
  case: bool_decide_reflect => [-> {t1}|neq'] /=.
  + by rewrite bool_decide_eq_false_2 //= bool_decide_eq_true_2.
  + rewrite IH. case: bool_decide_reflect => //= neq''.
    by rewrite bool_decide_eq_false_2.
Qed.

End Verif.

End AList.

Module SAList.

Definition new : val := λ: <>,
  ref (AList.empty #()).

Definition find : val := λ: "l" "k",
  AList.find !"l" "k".

Definition insert : val := λ: "l" "k" "v",
  "l" <- AList.insert !"l" "k" "v".

Definition delete : val := λ: "l" "k",
  "l" <- AList.delete !"l" "k".

Section Verif.

Context `{!cryptisGS Σ, !heapGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (γ : gname) (l : loc) (k t : term) (v kvs : val).
Implicit Types (db : gmap term val).

Definition is_alist v db : iProp := ∃ l kvs,
  ⌜v = #l⌝ ∗
  l ↦ kvs ∗
  ⌜AList.is_alist kvs db⌝.

Lemma wp_empty E :
  {{{ True }}}
    new #() @ E
  {{{ v, RET v; is_alist v ∅ }}}.
Proof.
iIntros "%Φ _ Hpost". wp_lam.
wp_bind (AList.empty _). iApply AList.wp_empty => //.
iIntros "!> %kvs %".
wp_alloc l as "Hl".
iModIntro. iApply "Hpost". iExists _. by eauto.
Qed.

Lemma wp_find E v db t :
  {{{ is_alist v db }}}
    find v t @ E
  {{{ RET (repr (db !! t)); is_alist v db }}}.
Proof.
iIntros "%Φ (%l & %kvs & -> & Hl & %) post".
wp_lam; wp_pures. wp_load.
iApply AList.wp_find => //.
iIntros "!> _". iApply "post".
iExists _. by eauto.
Qed.

Lemma wp_insert v db k v' E :
  {{{ is_alist v db }}}
    insert v k v' @ E
  {{{ RET #(); is_alist v (<[k := v']>db) }}}.
Proof.
iIntros "%Φ (%l & %kvs & -> & Hl & %) post".
wp_lam; wp_pures. wp_load.
wp_bind (AList.insert _ _ _). iApply AList.wp_insert => //.
iIntros "!> %r %". wp_store. iApply "post".
iExists _. by eauto.
Qed.

Lemma wp_delete v db k E :
  {{{ is_alist v db }}}
    delete v k @ E
  {{{ RET #(); is_alist v (base.delete k db) }}}.
Proof.
iIntros "%Φ (%l & %kvs & -> & Hl & %) post".
wp_lam; wp_pures. wp_load.
wp_bind (AList.delete _ _). iApply AList.wp_delete => //.
iIntros "!> %r %". wp_store. iApply "post".
iExists _. by eauto.
Qed.

End Verif.

End SAList.
