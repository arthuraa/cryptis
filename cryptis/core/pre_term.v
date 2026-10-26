From stdpp Require Import list_numbers.
From cryptis.core.pre_term Require Export base with_stdpp normalize.

(* [base.v] holds the datatype definitions, class instances and the lemmas about
   the comparison function; [normalize.v] holds the normalization machinery and
   the exponentiation laws.  We reassemble the pieces into a single [PreTerm]
   module here, so that clients can keep referring to [PreTerm.foo]. *)
Module PreTerm.
Include base.PreTerm.
Include normalize.PreTerm.

Fixpoint tsize (pt : pre_term) : nat :=
  match pt with
  | PT0 _ => 1
  | PT1 _ pt => S (tsize pt)
  | PT2 _ t1 t2 => S (tsize t1 + tsize t2)
  | PTN _ ps ns => S (sum_list_with tsize ps + sum_list_with tsize ns)
  end.

End PreTerm.

Export PreTerm.Exports.
