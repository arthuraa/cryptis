{
  description = "A separation logic for cryptographic protocols";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs";
  };

  outputs = { self, nixpkgs }:

    let pkgs = nixpkgs.legacyPackages.x86_64-linux; in {
          devShell.x86_64-linux =
            pkgs.mkShell {
              buildInputs = with pkgs; [
                coq
                coqPackages.mathcomp.ssreflect
                coqPackages.iris
                coqPackages.deriving
              ];
            };
        };
}
