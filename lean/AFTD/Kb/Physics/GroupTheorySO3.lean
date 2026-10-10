import AFTD.Prelude

/-!
# GroupTheory.SO3

Topic: classical_mechanics   Node: 0965259275dd

Provenance: formalization of a published result. Source: Physlib, `GroupTheory.SO3`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Groups/SO3/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The group of `3×3` real matrices with determinant 1 and `A * Aᵀ = 1`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
/-- The group of `3×3` real matrices with determinant 1 and `A * Aᵀ = 1`. -/
def GroupTheory.SO3 : Type := {A : Matrix (Fin 3) (Fin 3) ℝ // A.det = 1 ∧ A * Aᵀ = 1}
