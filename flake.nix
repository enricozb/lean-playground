{
  description = "lean 4 playground";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
  inputs.flake-utils.url = "github:numtide/flake-utils";

  inputs.lean-nix.url = "github:enricozb/lean.nix";

  inputs.mathlib-src = {
    url = "github:leanprover-community/mathlib4/v4.1.0";
    flake = false;
  };

  outputs = { self, nixpkgs, flake-utils, lean-nix, mathlib-src }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        leanPkgs = lean-nix.packages.${system};

        lean-mathlib = leanPkgs.lake2nix {
          name = "mathlib";
          src = mathlib-src;
        };

      in {
        devShells.default = pkgs.mkShell {
          packages = [
            lean-mathlib.package
            lean-mathlib.lean
            lean-mathlib.lean.vscode
          ];
        };
      });

}
