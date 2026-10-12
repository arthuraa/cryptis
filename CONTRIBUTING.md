# Contribution guidelines for this project

## Opaque definitions 

Use the locking mechanism of `elpi` to create opaque definitions:

```rocq
From elpi.apps Require Import locker.
lock Definition my_nat := 42.

(* Usage *)
Lemma my_natE : my_nat = 42.
Proof. by rewrite [my_nat]unlock. Qed.
```


