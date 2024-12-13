{
  description = "A separation logic for cryptographic protocols";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
    vscoq.url = "github:coq/vscoq";
    vscoq.inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs = { self, nixpkgs, flake-utils, vscoq }:
    flake-utils.lib.eachDefaultSystem (system:
      let pkgs = nixpkgs.legacyPackages.${system};
          lib = pkgs.lib; in rec {
            packages = rec {
              coq = pkgs.coq_8_18;
              coqPackages = pkgs.coqPackages_8_18.overrideScope (self: super:
                { mathcomp = super.mathcomp.override {
                    version = "1.18.0";
                  };
                });
            };

            devShell = pkgs.mkShell {
              packages = with packages; [
                coq
                coqPackages.mathcomp.ssreflect
                coqPackages.deriving
                coqPackages.iris
                # vscoq.packages.${system}.vscoq-language-server-coq-8-18
              ];
            };
          }
    );
}
