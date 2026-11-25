(** Finite functions from a type [T] ordered by a [Lexico] instance to a type
    [S] with a default value [d].

    [fmap T S d] maps all but finitely many keys to [d].  It is an
    association list sorted by keys whose values differ from [d], so each
    finite function has one representation: equality is extensional
    ([lookup_inj], [fmap_eq]) and decidable.

    [m !!! k] is the value of [k] in [m].  [∅] maps every key to [d],
    [{[k := v]}] maps [k] to [v] and every other key to [d], [<[k:=v]> m]
    sets [k] to [v], and [delete k m] resets [k] to [d].  [merge f m1 m2]
    combines two maps pointwise with [f] and has default [f d1 d2]; [map f m]
    applies [f] to every value and has default [f d].  [cast e m] moves [m]
    to an equal default [e : d1 = d2].  [to_list m] lists the keys whose
    value is not [d] with their values, sorted by keys, and [fmap_ind] builds
    a map by inserting one key at a time.  When [S] is
    ordered by a [Lexico] instance, so are finite maps, by their lists of
    bindings, so they can be keys of finite maps and elements of multisets. *)

From mathcomp Require Import ssreflect.
From stdpp Require Import sorting list proof_irrel lexico.

Module FMap.

(** ** Association lists *)

Section List.

Context {T : Type} `{EqDecision T, Lexico T}
  `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)}.

Implicit Types (k : T) (ks : list T).

Fixpoint keys {A} (l : list (T * A)) : list T :=
  match l with
  | [] => []
  | (k, _) :: l => k :: keys l
  end.

Lemma keys_fmap {A} (l : list (T * A)) : keys l = l.*1.
Proof. by elim: l => [|[k v] l IH] //=; rewrite IH. Qed.

Lemma lexico_keys {A} k k' (v : A) l :
  Forall (lexico k) (keys l) → (k', v) ∈ l → lexico k k'.
Proof.
elim: l => [|[k'' v''] l IH] /=; first by move=> _ /elem_of_nil.
by move=> /Forall_cons_iff [h /IH {}IH] /elem_of_cons [[-> _]|/IH].
Qed.

Lemma lexico_Forall_trans k k' ks :
  lexico k k' → Forall (lexico k') ks → Forall (lexico k) ks.
Proof. move=> kk'; apply: Forall_impl => k'' ?; by trans k'. Qed.

Lemma lexico_neq k k' : lexico k k' → k ≠ k'.
Proof. by move=> h e; subst; exact: (irreflexivity lexico k'). Qed.

Section Lookup.

Context {S : Type} `{EqDecision S} (d : S).

Implicit Types (v : S) (l : list (T * S)).

Definition wf l : bool :=
  bool_decide (StronglySorted lexico (keys l) ∧ Forall (λ kv, kv.2 ≠ d) l).

Fixpoint lookup_list k l : S :=
  match l with
  | [] => d
  | (k', v) :: l => if bool_decide (k = k') then v else lookup_list k l
  end.

Definition cons_nd k v l := if bool_decide (v = d) then l else (k, v) :: l.

Lemma lookup_list_lexico k l :
  Forall (lexico k) (keys l) → lookup_list k l = d.
Proof.
elim: l => [|[k' v] l IH] //= /Forall_cons_iff [kk' kl].
by rewrite bool_decide_false; [exact: lexico_neq kk'|exact: IH kl].
Qed.

Lemma lookup_cons_nd k v l k' : Forall (lexico k) (keys l) →
  lookup_list k' (cons_nd k v l) =
  if bool_decide (k' = k) then v else lookup_list k' l.
Proof.
rewrite /cons_nd => kl; case: (bool_decide_reflect (v = d)) => [->|_] //=.
by case: (bool_decide_reflect (k' = k)) => // ->; exact: lookup_list_lexico.
Qed.

Lemma cons_nd_lexico k k' v l : lexico k k' →
  Forall (lexico k) (keys l) → Forall (lexico k) (keys (cons_nd k' v l)).
Proof.
rewrite /cons_nd; case: (bool_decide_reflect (v = d)) => //= _ ??.
by constructor.
Qed.

Lemma cons_nd_sorted k v l :
  Forall (lexico k) (keys l) → StronglySorted lexico (keys l) →
  StronglySorted lexico (keys (cons_nd k v l)).
Proof.
rewrite /cons_nd; case: (bool_decide_reflect (v = d)) => //= _ ??.
by constructor.
Qed.

Lemma cons_nd_values k v l :
  Forall (λ kv, kv.2 ≠ d) l → Forall (λ kv, kv.2 ≠ d) (cons_nd k v l).
Proof.
rewrite /cons_nd; case: (bool_decide_reflect (v = d)) => // ??.
by constructor.
Qed.

Lemma lookup_list_inj l1 l2 : wf l1 → wf l2 →
  (∀ k, lookup_list k l1 = lookup_list k l2) → l1 = l2.
Proof.
move=> /bool_decide_unpack [s1 v1] /bool_decide_unpack [s2 v2].
elim: l1 l2 s1 v1 s2 v2 => [|[k1 a] l1 IH] [|[k2 b] l2] //=.
- move=> _ _ _ /Forall_cons_iff [/= nb _] /(_ k2).
  by rewrite bool_decide_true // => db; case: nb; rewrite db.
- move=> _ /Forall_cons_iff [/= na _] _ _ /(_ k1).
  by rewrite bool_decide_true // => ad; case: na.
move=> /StronglySorted_cons [lb1 s1] /Forall_cons_iff [/= na v1].
move=> /StronglySorted_cons [lb2 s2] /Forall_cons_iff [/= nb v2] e.
case: (trichotomyT lexico k1 k2) => [[k12|e12]|k21].
- move: (e k1); rewrite bool_decide_true // bool_decide_false.
    exact: lexico_neq.
  rewrite lookup_list_lexico; first exact: lexico_Forall_trans lb2.
  by move=> /na.
- subst k2; move: (e k1); rewrite !bool_decide_true // => <-.
  congr (_ :: _); apply: IH => // k; move: (e k).
  case: (bool_decide_reflect (k = k1)) => // ->.
  by rewrite !lookup_list_lexico.
- move: (e k2); rewrite bool_decide_false; first exact: lexico_neq.
  rewrite bool_decide_true // lookup_list_lexico.
    exact: lexico_Forall_trans lb1.
  by move=> db; case: nb; rewrite db.
Qed.

Lemma lookup_list_elem_of l k v :
  StronglySorted lexico (keys l) → Forall (λ kv, kv.2 ≠ d) l →
  (k, v) ∈ l ↔ lookup_list k l = v ∧ v ≠ d.
Proof.
elim: l => [|[k' v'] l IH] /=.
  by move=> _ _; split=> [/elem_of_nil|[<-]].
move=> /StronglySorted_cons [lb s] /Forall_cons_iff [/= nv' vs].
rewrite elem_of_cons; case: (bool_decide_reflect (k = k')) => [->|nk].
  split=> [[[->]|kl]|[<- _]]; [done| |by left].
  by case: (irreflexivity lexico k'); exact: (lexico_keys _ _ _ _ lb kl).
rewrite -IH //; split=> [[[ek _]|//]|?]; [by case: nk|by right].
Qed.

End Lookup.

Section Merge.

Context {S1 S2 S3 : Type} `{EqDecision S1, EqDecision S2, EqDecision S3}.
Context (d1 : S1) (d2 : S2) (f : S1 → S2 → S3).

Implicit Types (xs : list (T * S1)) (ys : list (T * S2)).

Fixpoint merge_list xs ys : list (T * S3) :=
  match xs with
  | [] => foldr (λ kb l, cons_nd (f d1 d2) kb.1 (f d1 kb.2) l) [] ys
  | (k1, a) :: xs' =>
    (fix go ys :=
       match ys with
       | [] => cons_nd (f d1 d2) k1 (f a d2) (merge_list xs' [])
       | (k2, b) :: ys' =>
         match trichotomyT lexico k1 k2 with
         | inleft (left _) =>
           cons_nd (f d1 d2) k1 (f a d2) (merge_list xs' ys)
         | inleft (right _) =>
           cons_nd (f d1 d2) k1 (f a b) (merge_list xs' ys')
         | inright _ => cons_nd (f d1 d2) k2 (f d1 b) (go ys')
         end
       end) ys
  end.

Lemma merge_list_lexico k xs ys :
  Forall (lexico k) (keys xs) → Forall (lexico k) (keys ys) →
  Forall (lexico k) (keys (merge_list xs ys)).
Proof.
elim: xs ys => [|[k1 a] xs IH1] ys.
  move=> _; elim: ys => [|[k2 b] ys IH2] //= /Forall_cons_iff [? ?].
  by apply: cons_nd_lexico => //; exact: IH2.
move=> /= /Forall_cons_iff [? lb1]; elim: ys => [|[k2 b] ys IH2] /=.
  by move=> _; apply: cons_nd_lexico => //; exact: IH1.
move=> /Forall_cons_iff [? lb2].
case: (trichotomyT lexico k1 k2) => [[_|_]|_]; apply: cons_nd_lexico => //.
- by apply: IH1 => //; constructor.
- exact: IH1.
- exact: IH2.
Qed.

Lemma merge_list_sorted xs ys :
  StronglySorted lexico (keys xs) → StronglySorted lexico (keys ys) →
  StronglySorted lexico (keys (merge_list xs ys)).
Proof.
elim: xs ys => [|[k1 a] xs IH1] ys.
  move=> _; elim: ys => [|[k2 b] ys IH2] //= /StronglySorted_cons [lb2 s2].
  apply: cons_nd_sorted; last exact: IH2.
  exact: (merge_list_lexico _ [] ys).
move=> /= /StronglySorted_cons [lb1 s1]; elim: ys => [|[k2 b] ys IH2] /=.
  move=> ?; apply: cons_nd_sorted; last exact: IH1.
  exact: (merge_list_lexico _ _ []).
move=> /StronglySorted_cons [lb2 s2].
case: (trichotomyT lexico k1 k2) => [[k12|e12]|k21].
- apply: cons_nd_sorted; last by apply: IH1 => //; constructor.
  apply: merge_list_lexico => //; constructor => //.
  exact: lexico_Forall_trans lb2.
- subst k2; apply: cons_nd_sorted; last exact: IH1.
  exact: merge_list_lexico.
- apply: cons_nd_sorted; last exact: IH2.
  apply: (merge_list_lexico _ ((k1, a) :: xs)) => //=; constructor => //.
  exact: lexico_Forall_trans lb1.
Qed.

Lemma merge_list_values xs ys :
  Forall (λ kv, kv.2 ≠ f d1 d2) (merge_list xs ys).
Proof.
elim: xs ys => [|[k1 a] xs IH1] ys.
  by elim: ys => [|[k2 b] ys IH2] //=; apply: cons_nd_values.
elim: ys => [|[k2 b] ys IH2] /=; first exact: cons_nd_values.
by case: (trichotomyT lexico k1 k2) => [[_|_]|_]; apply: cons_nd_values.
Qed.

Lemma lookup_merge_list k xs ys :
  StronglySorted lexico (keys xs) → StronglySorted lexico (keys ys) →
  lookup_list (f d1 d2) k (merge_list xs ys) =
  f (lookup_list d1 k xs) (lookup_list d2 k ys).
Proof.
elim: xs ys => [|[k1 a] xs IH1] ys.
  move=> _; elim: ys => [|[k2 b] ys IH2] //= /StronglySorted_cons [lb2 s2].
  rewrite lookup_cons_nd; first exact: (merge_list_lexico _ [] ys).
  by case: (bool_decide_reflect (k = k2)) => // _; exact: IH2.
move=> /= /StronglySorted_cons [lb1 s1]; elim: ys => [|[k2 b] ys IH2] /=.
  move=> ?; rewrite lookup_cons_nd; first exact: (merge_list_lexico _ _ []).
  by case: (bool_decide_reflect (k = k1)) => // _; exact: IH1.
move=> /StronglySorted_cons [lb2 s2].
case: (trichotomyT lexico k1 k2) => [[k12|e12]|k21].
- rewrite lookup_cons_nd.
    by apply: merge_list_lexico => //; constructor => //;
      exact: lexico_Forall_trans lb2.
  case: (bool_decide_reflect (k = k1)) => [->|_].
    rewrite bool_decide_false; first exact: lexico_neq.
    by rewrite lookup_list_lexico //; exact: lexico_Forall_trans lb2.
  by apply: IH1 => //; constructor.
- subst k2; rewrite lookup_cons_nd; first exact: merge_list_lexico.
  by case: (bool_decide_reflect (k = k1)) => // _; exact: IH1.
- rewrite lookup_cons_nd.
    apply: (merge_list_lexico _ ((k1, a) :: xs)) => //=.
    by constructor => //; exact: lexico_Forall_trans lb1.
  case: (bool_decide_reflect (k = k2)) => [->|_]; last exact: IH2.
  rewrite bool_decide_false; first exact: lexico_neq.
  by rewrite lookup_list_lexico //; exact: lexico_Forall_trans lb1.
Qed.

Lemma wf_merge_list xs ys :
  wf d1 xs → wf d2 ys → wf (f d1 d2) (merge_list xs ys).
Proof.
move=> /bool_decide_unpack [s1 _] /bool_decide_unpack [s2 _].
apply bool_decide_pack; split; first exact: merge_list_sorted.
exact: merge_list_values.
Qed.

End Merge.

End List.

(** ** Finite functions *)

Section FMap.

Context {T : Type} `{EqDecision T, Lexico T}
  `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)}.
Context {S : Type} `{EqDecision S} {d : S}.

Implicit Types (k : T) (v : S) (l : list (T * S)).

Record fmap := mk { car : list (T * S); wf_car : wf d car }.

Implicit Types (m : fmap).

Definition lookup k m : S := lookup_list d k (car m).

#[global] Arguments lookup : simpl never.

#[global] Instance lookup_total_instance : LookupTotal T S fmap := lookup.

Lemma car_inj m1 m2 : car m1 = car m2 → m1 = m2.
Proof.
case: m1 m2 => [l1 w1] [l2 w2] /= e; subst l2.
by rewrite (proof_irrel w1 w2).
Qed.

Lemma lookup_inj m1 m2 : (∀ k, m1 !!! k = m2 !!! k) → m1 = m2.
Proof.
move=> e; apply: car_inj; apply: (lookup_list_inj d).
- exact: wf_car.
- exact: wf_car.
- exact: e.
Qed.

Lemma fmap_eq m1 m2 : m1 = m2 ↔ ∀ k, m1 !!! k = m2 !!! k.
Proof. by split=> [->|]; last exact: lookup_inj. Qed.

#[global] Instance eq_dec : EqDecision fmap := λ m1 m2,
  match decide (car m1 = car m2) with
  | left e => left (car_inj m1 m2 e)
  | right n => right (λ e, n (f_equal car e))
  end.

Lemma wf_singleton k v : wf d (cons_nd d k v []).
Proof.
apply bool_decide_pack; split.
- by apply: cons_nd_sorted; constructor.
- by apply: cons_nd_values; constructor.
Qed.

#[global] Instance empty_instance : Empty fmap :=
  mk [] (bool_decide_pack _ (conj (SSorted_nil _) (Forall_nil _))).

#[global] Instance singleton_instance : SingletonM T S fmap :=
  λ k v, mk (cons_nd d k v []) (wf_singleton k v).

Lemma lookup_empty k : (∅ : fmap) !!! k = d.
Proof. done. Qed.

Lemma lookup_singleton k k' v :
  ({[k' := v]} : fmap) !!! k = if bool_decide (k = k') then v else d.
Proof.
by rewrite /lookup_total /lookup_total_instance /lookup /= lookup_cons_nd.
Qed.

Definition to_list m : list (T * S) := car m.

Lemma to_list_sorted m : StronglySorted lexico (to_list m).*1.
Proof. by rewrite -keys_fmap; have /bool_decide_unpack [] := wf_car m. Qed.

Lemma elem_of_to_list m k v : (k, v) ∈ to_list m ↔ m !!! k = v ∧ v ≠ d.
Proof.
have /bool_decide_unpack [s vs] := wf_car m.
exact: lookup_list_elem_of.
Qed.

Lemma to_list_singleton k v : v ≠ d → to_list {[k := v]} = [(k, v)].
Proof.
move=> nv; rewrite /to_list /singletonM /singleton_instance /= /cons_nd.
by rewrite bool_decide_false.
Qed.

End FMap.

Arguments fmap T {_ _ _} S {_} d.

Section Merge.

Context {T : Type} `{EqDecision T, Lexico T}
  `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)}.
Context {S1 S2 S3 : Type} `{EqDecision S1, EqDecision S2, EqDecision S3}.
Context {d1 : S1} {d2 : S2}.

Definition merge (f : S1 → S2 → S3) (m1 : fmap T S1 d1) (m2 : fmap T S2 d2) :
    fmap T S3 (f d1 d2) :=
  mk (merge_list d1 d2 f (car m1) (car m2))
    (wf_merge_list d1 d2 f _ _ (wf_car m1) (wf_car m2)).

Lemma lookup_merge f m1 m2 k :
  merge f m1 m2 !!! k = f (m1 !!! k) (m2 !!! k).
Proof.
have /bool_decide_unpack [s1 _] := wf_car m1.
have /bool_decide_unpack [s2 _] := wf_car m2.
exact: lookup_merge_list.
Qed.

End Merge.

Section Insert.

Context {T : Type} `{EqDecision T, Lexico T}
  `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)}.
Context {S : Type} `{EqDecision S} {d : S}.

Implicit Types (k : T) (v : S) (m : fmap T S d).

(* Every update is a merge, so only [merge_list] needs list-level proofs. *)
#[global] Instance insert_instance : Insert T S (fmap T S d) :=
  λ k v m, merge (λ a o, default a o) m ({[k := Some v]} : fmap T _ None).

#[global] Instance delete_instance : Delete T (fmap T S d) :=
  λ k m, <[k:=d]> m.

Lemma lookup_insert m k k' v :
  <[k':=v]> m !!! k = if bool_decide (k = k') then v else m !!! k.
Proof.
rewrite /insert /insert_instance lookup_merge lookup_singleton.
by case: (bool_decide_reflect (k = k')).
Qed.

Lemma lookup_delete m k k' :
  delete k' m !!! k = if bool_decide (k = k') then d else m !!! k.
Proof. exact: lookup_insert. Qed.

Lemma fmap_ind (P : fmap T S d → Prop) :
  P ∅ → (∀ k v m, m !!! k = d → v ≠ d → P m → P (<[k:=v]> m)) → ∀ m, P m.
Proof.
move=> P0 PS [l w]; elim: l w => [|[k v] l IH] w.
  by have -> : mk [] w = ∅ by apply: car_inj.
have /bool_decide_unpack [/= /StronglySorted_cons [lb s]] := w.
move=> /Forall_cons_iff [/= nv vs].
have w' : wf d l by apply bool_decide_pack.
have -> : mk ((k, v) :: l) w = <[k:=v]> (mk l w').
  apply: lookup_inj => k'; rewrite lookup_insert.
  by rewrite /lookup_total /lookup_total_instance /lookup.
apply: PS; [exact: (lookup_list_lexico d k l)|done|exact: IH].
Qed.

End Insert.

Section Map.

Context {T : Type} `{EqDecision T, Lexico T}
  `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)}.
Context {S1 S2 : Type} `{EqDecision S1, EqDecision S2} {d1 : S1}.

Definition map (f : S1 → S2) (m : fmap T S1 d1) : fmap T S2 (f d1) :=
  merge (λ a (_ : unit), f a) m (∅ : fmap T unit tt).

Lemma lookup_map f m k : map f m !!! k = f (m !!! k).
Proof. exact: lookup_merge. Qed.

End Map.

Section Cast.

Context {T : Type} `{EqDecision T, Lexico T}
  `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)}.
Context {S : Type} `{EqDecision S}.

(* Only the proof field mentions [e], so the bindings still compute. *)
Definition cast {d1 d2 : S} (e : d1 = d2) (m : fmap T S d1) : fmap T S d2 :=
  mk (car m)
    (match e in _ = d return wf d (car m) with eq_refl => wf_car m end).

Lemma to_list_cast d1 d2 (e : d1 = d2) (m : fmap T S d1) :
  to_list (cast e m) = to_list m.
Proof. done. Qed.

Lemma lookup_cast d1 d2 (e : d1 = d2) (m : fmap T S d1) k :
  cast e m !!! k = m !!! k.
Proof. by case: d2 / e. Qed.

End Cast.

Section Lexico.

Context {T : Type} `{EqDecision T, Lexico T}
  `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)}.
Context {S : Type} `{EqDecision S, Lexico S}
  `{!StrictOrder (@lexico S _), !TrichotomyT (@lexico S _)} {d : S}.

#[global] Instance lexico_instance : Lexico (fmap T S d) :=
  λ m1 m2, lexico (to_list m1) (to_list m2).

#[global] Instance lexico_strict : StrictOrder (@lexico (fmap T S d) _).
Proof.
split; first by move=> m; exact: (irreflexivity lexico (to_list m)).
move=> m1 m2 m3; exact: (@transitivity _ (@lexico (list (T * S)) _) _).
Qed.

#[global] Instance lexico_trichotomyT : TrichotomyT (@lexico (fmap T S d) _).
Proof.
refine (λ m1 m2,
  match trichotomyT lexico (to_list m1) (to_list m2) with
  | inleft (left p) => inleft (left p)
  | inleft (right e) => inleft (right _)
  | inright p => inright p
  end).
abstract (exact: car_inj e).
Defined.

End Lexico.

End FMap.
