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
              coq = pkgs.coq_9_0;
              coqPackages = pkgs.coqPackages_9_0;
            };

            devShell = pkgs.mkShell {
              packages = with packages; [
                coq
                coqPackages.mathcomp.ssreflect
                coqPackages.deriving
                coqPackages.iris
                # coqPackages.vscoq-language-server
              ];
            };
          }
    );
}
