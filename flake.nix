{
  description = "A separation logic for cryptographic protocols";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let pkgs = nixpkgs.legacyPackages.${system};
          lib = pkgs.lib; in rec {
            packages = rec {
              coq = pkgs.coq_8_18;
              coqPackages = pkgs.coqPackages_8_18.overrideScope (self: super:
                { mathcomp = super.mathcomp.override {
                    version = "1.17.0";
                  };
                });
            };

            devShell = pkgs.mkShell {
              packages = with packages; [
                coq
                coqPackages.mathcomp.ssreflect
                coqPackages.deriving
                coqPackages.iris
              ];
            };
          }
    );
}
