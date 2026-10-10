import AFTD.Prelude

/-!
# Matrix.crossProductMatrix

Topic: classical_mechanics   Node: dcccd2f06e50

Provenance: formalization of a published result. Source: Physlib, `Matrix.crossProductMatrix`. Lean proof by Giuseppe Sorge, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Modules/CrossProductMatrix.lean (Copyright (c) 2026 Giuseppe Sorge. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The hat map `[ω]ₓ`: the skew-symmetric `3 × 3` matrix acting as the cross product with `ω`, i.e. `[ω]ₓ *ᵥ v = ω ⨯₃ v`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The hat map `[ω]ₓ`: the skew-symmetric `3 × 3` matrix acting as the cross product with `ω`, i.e. `[ω]ₓ *ᵥ v = ω ⨯₃ v`. -/
def Matrix.crossProductMatrix (ω : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, -ω 2, ω 1; ω 2, 0, -ω 0; -ω 1, ω 0, 0]
