{
  description = "A separation logic for cryptographic protocols";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs";
    flake-parts.url = "github:hercules-ci/flake-parts";
    nix-github-actions.url = "github:nix-community/nix-github-actions";
    nix-github-actions.inputs.nixpkgs.follows = "nixpkgs";
    # nixpkgs has no coq-lsp for Rocq 9.2, and rocq-lsp has no 9.2 release yet;
    # build its v9.2 branch.
    rocq-lsp.url = "github:rocq-community/rocq-lsp/v9.2";
    rocq-lsp.flake = false;
    # rocq-mcp is pure Python and independent of the Rocq version, so it does
    # not follow our nixpkgs: with ours, its dependency chain pulls in
    # python3-inline-snapshot, whose test suite fails.  Pin the revision
    # rocq-mcp's own flake.lock was tested against.
    rocq-mcp.url = "github:arthuraa/rocq-mcp-flake";
    rocq-mcp.inputs.nixpkgs.url = "github:NixOS/nixpkgs/8f21ecf6d80d56dd43f4c7c9191fb805aa8ac98f";
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
            pkgs.rocqPackages.coq-lsp
          ];
          inputsFrom = [
            self'.packages.default
          ];
        };

        devShells.ai = pkgs.mkShell {
          propagatedBuildInputs = [
            pkgs.rocqPackages.coq-lsp
            inputs'.rocq-mcp.packages.rocq-mcp
          ];
          inputsFrom = [
            self'.packages.default
          ];
        };

        # Equivalent to  inputs'.nixpkgs.legacyPackages.hello;
        packages.default = pkgs.rocqPackages.cryptis;

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
          rocqPackages = prev.rocqPackages_9_2.overrideScope (final: prev: {
            coq-lsp = prev.coq-lsp.override {
              version = inputs.rocq-lsp.outPath;
            };
            cryptis = prev.mkRocqDerivation {
              pname = "cryptis";
              version = ./.;
              propagatedBuildInputs = [
                final.rocq-core
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
