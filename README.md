# Verifying cryptographic protocols with logical relations

- `basic.v`: Basic infrastructure for reasoning about contextual
  approximation. Mostly stolen from Iris.
  
- `symbols.v`: An implementation of a symbol datatype with references, which we
  will use to implement cryptographic secrets such as nonces and keys.  When
  proving a contextual approximation, we can reason about symbols that are in
  correspondence in the two sides of the statement (i.e., because they were
  allocated in parallel), or that exist in only one side of the statement (i.e.,
  because one of the sides ran a symbol-allocation command that was not matched
  on the other side).
  
- `crypto.v`: A logical relation for reasoning about cryptographic terms. Work
  in progress.
