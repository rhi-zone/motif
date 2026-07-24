import Lake
open Lake DSL

package «langlands» where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.32.1"

@[default_target]
lean_lib «Langlands» where
  -- add library configuration options here
