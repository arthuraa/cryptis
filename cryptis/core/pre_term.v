From cryptis.core.pre_term Require Export base with_stdpp normalize.

(* [base.v] holds the datatype definitions, class instances and the lemmas about
   the comparison function; [normalize.v] holds the rest of the pre-term theory
   (the stdpp-based development).  We reassemble both halves into a single
   [PreTerm] module here, so that clients can keep referring to [PreTerm.foo] as
   before. *)
Module PreTerm.
Include base.PreTerm.
Include normalize.PreTerm.
End PreTerm.

Export PreTerm.Exports.
