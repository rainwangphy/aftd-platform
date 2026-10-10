import AFTD.Prelude

/-!
# spaceTime.γ.diracForm

Topic: special_relativity   Node: d51aad5016da

Provenance: formalization of a published result. Source: Physlib, `spaceTime.γ.diracForm`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/CliffordAlgebra.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The quadratic form of the Clifford algebra corresponding to the gamma matrices.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Complex in
/-- The quadratic form of the Clifford algebra corresponding to the gamma matrices. -/
@[simps!]
noncomputable def spaceTime.γ.diracForm : QuadraticForm ℝ (Fin 4 → ℝ) :=
  QuadraticMap.sq.comp (LinearMap.proj 0)
    - QuadraticMap.sq.comp (LinearMap.proj 1)
    - QuadraticMap.sq.comp (LinearMap.proj 2)
    - QuadraticMap.sq.comp (LinearMap.proj 3)
