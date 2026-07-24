{
  description = "langlands - Lean 4 + Mathlib project (subproject of motif)";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
      in
      {
        devShells.default = pkgs.mkShell {
          buildInputs = with pkgs; [
            elan
          ];

          # elan downloads prebuilt, dynamically-linked Lean toolchains that expect
          # an FHS-style dynamic linker. On NixOS these won't run out of the box;
          # nix-ld (or an equivalent /lib64/ld-linux-x86-64.so.2 shim) is required.
          # See langlands/README.md for details.
          shellHook = ''
            export PATH="$HOME/.elan/bin:$PATH"
          '';
        };
      }
    );
}
