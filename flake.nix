{
  description = "A separation logic for cryptographic protocols";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs";
    flake-parts.url = "github:hercules-ci/flake-parts";
    nix-github-actions.url = "github:nix-community/nix-github-actions";
    nix-github-actions.inputs.nixpkgs.follows = "nixpkgs";
    actris.url = "git+https://gitlab.mpi-sws.org/iris/actris.git?rev=fa669607568fbf897f6551b7bc9e912b10e1b577";
    actris.flake = false;
  };

  outputs = inputs@{ self, flake-parts, nixpkgs, nix-github-actions, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      imports = [
        # To import a flake module
        # 1. Add foo to inputs
        # 2. Add foo as a parameter to the outputs function
        # 3. Add here: foo.flakeModule

      ];
      systems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" "x86_64-darwin" ];
      perSystem = { config, self', inputs', pkgs, system, ... }: {
        _module.args.pkgs = import nixpkgs {
          inherit system;
          overlays = [ self.overlays.default ];
        };

        # Per-system attributes can be defined here. The self' and inputs'
        # module parameters provide easy access to attributes of the same
        # system.

        devShells.default = pkgs.mkShell {
          propagatedBuildInputs = [
            pkgs.coqPackages.coq-lsp
          ];
          inputsFrom = [
            self'.packages.default
          ];
        };

        # Equivalent to  inputs'.nixpkgs.legacyPackages.hello;
        packages.default = pkgs.coqPackages.cryptis;

        checks.default = self'.packages.default;

      };
      flake = {

        # The usual flake attributes can be defined here, including system-
        # agnostic ones like nixosModule and system-enumerating ones, although
        # those are more easily expressed in perSystem.

        githubActions = nix-github-actions.lib.mkGithubMatrix {
          checks = nixpkgs.lib.getAttrs
            [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" ]
            self.checks;
        };

        overlays.default = final: prev: {
          coqPackages = prev.coqPackages_9_1.overrideScope (final: prev: {
            actris = prev.mkCoqDerivation {
              pname = "actris";
              defaultVersion = "dev";
              release.dev.src = inputs.actris;
              propagatedBuildInputs = [
                final.coq
                final.iris
              ];
              # The actris repository bundles experimental side developments
              # (multris, linking_actris, linear_actris) that lag behind the
              # iris release; build and install only the core actris/ library.
              preBuild = ''
                patchShebangs .
                for f in _CoqProject _RocqProject; do
                  if [ -f "$f" ]; then
                    grep -E '^(-.*|actris/.*)$' "$f" > "$f".new
                    mv "$f".new "$f"
                  fi
                done
              '';
            };
            cryptis = prev.mkCoqDerivation {
              pname = "cryptis";
              version = ./.;
              propagatedBuildInputs = [
                final.coq
                final.mathcomp.ssreflect
                final.deriving
                final.iris
                final.actris
                final.stdlib
              ];
            };
          });
        };

      };
    };
}
