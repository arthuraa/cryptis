with import <nixpkgs> {};

let coq = coq_8_13; in
let coqPackages = coqPackages_8_13; in
let ocaml = coq.ocamlPackages.ocaml; in
let ssreflect = coqPackages.mathcomp.ssreflect; in

let mkCoqDerivation =
  import <nixpkgs/pkgs/build-support/coq> {
    inherit lib stdenv coqPackages coq fetchzip;
}; in

let stdpp = with lib; mkCoqDerivation rec {
  pname = "stdpp";
  domain = "gitlab.mpi-sws.org";
  owner = "iris";
  version = "20210728";
  defaultVersion = "20210728";
  release."20210728".rev = "644197152ae14de2b419dfb08ddcc8b53d4121cf";
  release."20210728".sha256 = "sha256:0pwn2qwdzndsshkam4spmydrn35hw4cxain0vb3gy15slqyvrkxn";
  releaseRev = v: "coq-stdpp-${v}";
  patchPhase = ''
    patchShebangs coq-lint.sh
  '';

  meta = {
    description = "An extended “Standard Library” for Coq";
    license = licenses.bsd3;
    maintainers = [ maintainers.vbgl ];
  };

};
in

let iris = with lib; mkCoqDerivation rec {
  pname = "iris";
  domain = "gitlab.mpi-sws.org";
  owner = "iris";
  version = "20210728";
  defaultVersion = "20210728";
  release."20210728".rev = "e51adf8d818f0ba5646e028e5c99b4483caef94d";
  release."20210728".sha256 = "sha256:0f2ar9l4q9mxilsm5bk79xzrih7z5sswm1fyj7jfrgq0x17abp8d";
  propagatedBuildInputs = [ stdpp ];
  patchPhase = ''
    patchShebangs coq-lint.sh
  '';
};
in

let deriving = with lib; mkCoqDerivation rec {
  pname = "deriving";
  domain = "github.com";
  owner = "arthuraa";
  version = "0.1.0";
  defaultVersion = "0.1.0";
  release."0.1.0".sha256 = "sha256:11crnjm8hyis1qllkks3d7r07s1rfzwvyvpijya3s6iqfh8c7xwh";
  releaseRev = (v: "v${v}");
  propagatedBuildInputs = [ ocaml ssreflect ];
  preBuild = ''
    substituteInPlace CoqMakefile.local --replace ocaml ${ocaml}/bin/ocaml
  '';
};
in

mkShell {
  packages = [ coq stdpp iris ocaml ssreflect deriving ];
}
