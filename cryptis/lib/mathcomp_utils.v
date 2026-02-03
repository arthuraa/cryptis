From mathcomp Require Import all_boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma perm_rem (T : eqType) (x : T) s1 s2 :
  perm_eq s1 s2 -> perm_eq (rem x s1) (rem x s2).
Proof.
move=> s1s2; apply/permP => P.
by rewrite !count_rem (permP s1s2) (perm_mem s1s2).
Qed.

Lemma rem_rem (T : eqType) (x y : T) (s: seq T) :
  rem x (rem y s) = rem y (rem x s).
Proof.
elim: s => [| z s IH] //=.
have [-> | zy //=] := altP (z =P y).
  - have [-> // | yx] := altP (y =P x).
    by rewrite /= eqxx.
  - have [//= | zx /=] := altP (z =P x).
    by rewrite (negbTE zy) IH.
Qed.
