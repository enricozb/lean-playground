{
  description = "lean 4 playground";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
  inputs.flake-utils.url = "github:numtide/flake-utils";

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        lean2nix = import /home/enricozb/projects/nix/lean.nix/default.nix;
        mathlib = lean2nix {
          name = "mathlib";
          src = "https://github.com/leanprover-community/mathlib4";
        };

      in {
        devShells.default =
          pkgs.mkShell { packages = [ lean mathlib vscode ]; };
      });

}
