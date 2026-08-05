import Mathlib

/-!
# Smoke test

Elaboration checks confirming that the Mathlib dependency resolves and elaborates. No
mathematical content.
-/

#check (2 : ℤ) + 2 = 4
#check @Continuous.add
#check MonoidHom
