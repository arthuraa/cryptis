{
  description = "A separation logic for cryptographic protocols";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/c4d5ad04f949c1c0b22f48c3917bc2f8a969b729";
    flake-utils.url = "github:numtide/flake-utils";
    actris.url = "git+https://gitlab.mpi-sws.org/iris/actris.git?rev=7502c27c8e6d1ff7d824a6eb23cab6223acff3f1";
    actris.flake = false;
    iris-dev.url = "git+https://gitlab.mpi-sws.org/iris/iris.git?rev=fa344cbe1a781fdc8c6263fbe18de976b6920751";
    iris-dev.flake = false;
    stdpp.url = "git+https://gitlab.mpi-sws.org/iris/stdpp.git?ref=refs/tags/coq-stdpp-1.12.0";
    stdpp.flake = false;
  };

  outputs = { self, nixpkgs, flake-utils, actris, iris-dev, stdpp }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs =
          import nixpkgs {
            inherit system;
            overlays = [ self.overlays.default ];
          };
      in
        {
          devShell = pkgs.mkShell {
            packages = [
              pkgs.coq
              pkgs.coqPackages.mathcomp.ssreflect
              pkgs.coqPackages.deriving
              pkgs.coqPackages.iris
              pkgs.coqPackages.actris
              nixpkgs.legacyPackages.${system}.coqPackages.coq-lsp
            ];
          };
        }
    ) //
    {
      overlays.default = final: prev: {
        coqPackages = prev.coqPackages.overrideScope (final: prev: {
          stdpp = prev.mkCoqDerivation {
            pname = "stdpp";
            defaultVersion = "1.12";
            release."1.12".src = stdpp;
            propagatedBuildInputs = [
              final.coq
              final.stdlib
            ];
            preBuild = ''
              patchShebangs .
            '';
          };

          iris = prev.mkCoqDerivation {
            pname = "iris";
            defaultVersion = "dev";
            release.dev.src = iris-dev;
            propagatedBuildInputs = [
              final.coq
              final.stdpp
            ];
            preBuild = ''
              patchShebangs .
            '';
          };

          actris = prev.mkCoqDerivation {
            pname = "actris";
            defaultVersion = "dev";
            release.dev.src = actris;
            propagatedBuildInputs = [
              final.coq
              final.iris
            ];
            preBuild = ''
              patchShebangs .
            '';
          };
        });
      };
    };
}
