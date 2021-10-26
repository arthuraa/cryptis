with import <nixpkgs> {};

let coq = coq_8_13; in
let coqPackages = coqPackages_8_13; in
let ssreflect = coqPackages.mathcomp.ssreflect; in
let deriving = coqPackages.deriving; in

let
  stdpp_ = coqPackages.stdpp.override {
    version = "644197152ae14de2b419dfb08ddcc8b53d4121cf";
  };

  iris_ = coqPackages.iris.override {
    version = "e51adf8d818f0ba5646e028e5c99b4483caef94d";
  };

  stdpp = stdpp_.overrideAttrs (o: {
    patchPhase = ''
      patchShebangs coq-lint.sh
    '';
  });

  iris = iris_.overrideAttrs (o: {
    patchPhase = ''
      patchShebangs coq-lint.sh
    '';
    propagatedBuildInputs = [ stdpp ];
  });

in

mkShell {
  packages = [ coq stdpp iris ssreflect deriving ];
}
