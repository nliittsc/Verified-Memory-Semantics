# Docs on agda in nix:
#
#   https://nixos.org/manual/nixpkgs/stable/#agda
#   https://nixos.org/manual/nixpkgs/stable/#compiling-agda
#   https://nixos.org/manual/nixpkgs/stable/#building-agda-packages
#   http://ryantm.github.io/nixpkgs/languages-frameworks/agda/

{
  description = "Verified-Memory-Semantics";

  inputs = {
    nixpkgs.url = github:NixOS/nixpkgs/nixos-21.05;
    flake-utils.url = github:numtide/flake-utils;
  };

  outputs = { self, nixpkgs, flake-utils }: flake-utils.lib.eachDefaultSystem (system:
    with (import nixpkgs { inherit system; });
    {
      defaultPackage =
        agdaPackages.mkDerivation {
          pname = "Verified-Memory-Semantics";
          version = "0.0";
          src = nix-gitignore.gitignoreSource [ "*.nix" "flake.lock" "result" "build-env" ] ./.;
          buildInputs = [
            agdaPackages.standard-library
          ];
        };
      devShell =
        mkShell {
          name = "agda-dev_" + self.defaultPackage.${system}.pname;
          buildInputs = self.defaultPackage.${system}.buildInputs;
        };
    });
}
