From mathcomp Require Import ssreflect.
From stdpp Require Import list_numbers.
From cryptis.core.pre_term Require Export base with_stdpp normalize.

(* [base.v] holds the datatype definitions, class instances and the lemmas about
   the comparison function; [normalize.v] holds the normalization machinery and
   the exponentiation laws.  We reassemble the pieces into a single [PreTerm]
   module here, so that clients can keep referring to [PreTerm.foo]. *)
Module PreTerm.
Include base.PreTerm.
Include normalize.PreTerm.

(* A Diffie-Hellman pre-term is as large as the product of its factors [b ^ p]
   ([gfactors]), so that a factor of a group product is smaller than the
   product. *)
Fixpoint tsize (pt : pre_term) : nat :=
  match pt with
  | PT0 _ => 1
  | PT1 _ pt => S (tsize pt)
  | PT2 _ t1 t2 => S (tsize t1 + tsize t2)
  | PTMul ps ns => S (sum_list_with tsize ps + sum_list_with tsize ns)
  | PTDH [(b, ([e], []))] => S (tsize b + tsize e)
  | PTDH l =>
    let fsize b p :=
      match p with
      | PTMul [] [] => tsize b
      | _ => S (tsize b + tsize p)
      end in
    S (sum_list_with (λ e,
         sum_list_with (fsize e.1) e.2.1 + sum_list_with (fsize e.1) e.2.2) l)
  end.

Definition fsize b p :=
  match p with
  | PTMul [] [] => tsize b
  | _ => S (tsize b + tsize p)
  end.

Lemma tsize_mk_exp b p : tsize (mk_exp b p) = fsize b p.
Proof.
rewrite /mk_exp; case: (bool_decide_reflect (p = PTMul [] [])) => [->|np] //.
by case: p np => [?|??|???|[|??] [|??]|?] //; case.
Qed.

Lemma tsize_gmul_dh l :
  is_gmul (PTDH l) → tsize (PTDH l) = S (sum_list_with tsize (dh_elements l)).
Proof.
have -> : sum_list_with tsize (dh_elements l) =
          sum_list_with (λ e, sum_list_with (fsize e.1) e.2.1 +
                              sum_list_with (fsize e.1) e.2.2) l.
  elim: l => [//|[b [ps ns]] l IH] /=.
  have sumE qs : sum_list_with tsize (mk_exp b <$> qs) =
                 sum_list_with (fsize b) qs.
    by elim: qs => [//|q qs IHq] /=; rewrite tsize_mk_exp IHq.
  by rewrite sum_list_with_app IH fmap_app sum_list_with_app !sumE.
by case: l => [|[b [[|e [|??]] [|??]]] [|??]].
Qed.

End PreTerm.

Export PreTerm.Exports.
