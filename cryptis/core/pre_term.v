From mathcomp Require Import ssreflect.
From stdpp Require Import list_numbers.
From cryptis.lib Require Import list_sort fmap mset sms poly poly_gcd frac.
From cryptis.core.pre_term Require Export base with_stdpp normalize gfactors
  factors tsize.

(* The pre-term layer is split by topic: [base.v] defines the datatype and its
   order, [normalize.v] normal forms, [gfactors.v] group factors, [factors.v]
   factors of exponents and [tsize.v] sizes.  We reassemble the pieces into a
   single [PreTerm] module here, so that clients can keep referring to
   [PreTerm.foo]. *)
Module PreTerm.
Include base.PreTerm.
Include normalize.PreTerm.
Include gfactors.PreTerm.
Include factors.PreTerm.
Include tsize.PreTerm.
End PreTerm.

Export PreTerm.Exports.
