with import <nixpkgs> {};

let coq = coq_8_15; in
let coqPackages = coqPackages_8_15; in
let ssreflect = coqPackages.mathcomp.ssreflect; in
let deriving = coqPackages.deriving; in
let stdpp = coqPackages.stdpp; in
let iris  = coqPackages.iris; in

mkShell {
  packages = [ coq stdpp iris ssreflect deriving ];
}
