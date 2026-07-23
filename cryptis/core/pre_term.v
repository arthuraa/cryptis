From cryptis.core.pre_term Require Export base theory with_stdpp.

(* [base.v] holds the datatype definitions, class instances and the lemmas about
   the comparison function; [theory.v] holds the rest of the pre-term theory.
   We reassemble both halves into a single [PreTerm] module here, so that clients
   can keep referring to [PreTerm.foo] as before. *)
Module PreTerm.
Include base.PreTerm.
Include theory.PreTerm.
End PreTerm.

Export PreTerm.Exports.
