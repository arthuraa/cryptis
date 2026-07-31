From cryptis.core.pre_term Require Export base with_stdpp normalize laws.

(* [base.v] holds the datatype definitions, class instances and the lemmas about
   the comparison function; [normalize.v] holds the normalization machinery; and
   [laws.v] holds the algebraic theory of the operations and destructors.  We
   reassemble the pieces into a single [PreTerm] module here, so that clients can
   keep referring to [PreTerm.foo] as before. *)
Module PreTerm.
Include base.PreTerm.
Include normalize.PreTerm.
Include laws.PreTerm.
End PreTerm.

Export PreTerm.Exports.
