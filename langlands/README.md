# langlands

Lean 4 + Mathlib project (subproject of [motif](../README.md)).

## Setup

This subdirectory has its own `flake.nix` (separate from the root motif flake,
which only provisions the Rust toolchain). It provides `elan`, the Lean
version manager, via nixpkgs.

```bash
cd langlands
nix develop        # provides elan; installs the pinned toolchain on first use
lake update         # fetch Mathlib and its transitive dependencies
lake exe cache get  # download prebuilt Mathlib .olean files (avoids a from-source build)
lake build          # build this project (Langlands.lean, Langlands/Basic.lean)
```

The toolchain is pinned in `lean-toolchain` to match the Mathlib version
pinned in `lakefile.lean` (`require mathlib from git ... @ "vX.Y.Z"`) — both
must be bumped together when upgrading Mathlib.

`elan` downloads a prebuilt, dynamically linked Lean toolchain. This worked
directly in this environment; on a stricter NixOS setup without `nix-ld` (or
equivalent), the downloaded binary may fail to run with a missing dynamic
linker error, in which case enable `programs.nix-ld.enable = true;` in your
NixOS configuration.

## Layout

- `lakefile.lean` — Lake build file, Mathlib dependency pin
- `lean-toolchain` — Lean version, must match the Mathlib version's own
  `lean-toolchain`
- `Langlands.lean` — root module (imports the library's modules)
- `Langlands/Basic.lean` — starter file; imports `Mathlib` and has sanity
  `#check`s to confirm the dependency resolves and compiles
