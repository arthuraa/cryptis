{
  description = "A separation logic for cryptographic protocols";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
    actris.url = "git+https://gitlab.mpi-sws.org/iris/actris.git";
    actris.flake = false;
    stdpp-1-12.url = "git+https://gitlab.mpi-sws.org/iris/stdpp.git?ref=refs/tags/coq-stdpp-1.12.0";
    stdpp-1-12.flake = false;
  };

  # outputs = { self, nixpkgs, stdpp, flake-utils }:
  outputs = { self, nixpkgs, flake-utils, actris, stdpp-1-12 }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs =
          import nixpkgs {
            inherit system;
            overlays = [ self.overlays.default ];
          };
        lib = pkgs.lib;
      in
        {
          devShell = pkgs.mkShell {
            packages = [
              pkgs.coq
              pkgs.coqPackages.mathcomp.ssreflect
              pkgs.coqPackages.deriving
              pkgs.coqPackages.iris
              pkgs.coqPackages.actris
            ];
          };
        }
    ) //
    {
      overlays.default = final: prev: {
        coqPackages = prev.coqPackages.overrideScope (final: prev: {
          actris = prev.mkCoqDerivation {
            pname = "actris";
            defaultVersion = "dev";
            release.dev.src = actris;
            propagatedBuildInputs = [
              final.coq
              final.iris
            ];
          };

          stdpp = prev.lib.overrideCoqDerivation {
            defaultVersion = "1.12";
            release."1.12".src = stdpp-1-12;
          } prev.stdpp;
        });
      };
    };
}
