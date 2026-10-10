import AFTD.Prelude
import AFTD.Kb.Physics.KroneckerDeltaGeneralizedKroneckerDelta
import AFTD.Kb.Physics.KroneckerDeltaKroneckerDelta

/-!
# KroneckerDelta.generalizedKroneckerDelta_swap

Topic: classical_mechanics   Node: 34924b879610

Provenance: formalization of a published result. Source: Physlib, `KroneckerDelta.generalizedKroneckerDelta_swap`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/KroneckerDelta/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Swapping two of the upper indices of the generalized Kronecker delta negates it. This is one row transposition of the underlying determinant.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open KroneckerDelta in
variable {α M : Type*} [DecidableEq α] in
open Matrix in
/-- Swapping two of the upper indices of the generalized Kronecker delta negates it. This is one row transposition of the underlying determinant. -/
lemma KroneckerDelta.generalizedKroneckerDelta_swap {α ι : Type} [DecidableEq α] [DecidableEq ι] [Fintype ι]
    (μ ν : ι → α) {i j : ι} (hij : i ≠ j) :
    generalizedKroneckerDelta (μ ∘ Equiv.swap i j) ν = - generalizedKroneckerDelta μ ν := by
  show (Matrix.submatrix (Matrix.of fun a b => ((kroneckerDelta (μ a) (ν b) : ℕ) : ℤ))
      (Equiv.swap i j) id).det
    = -(Matrix.of fun a b => ((kroneckerDelta (μ a) (ν b) : ℕ) : ℤ)).det
  rw [Matrix.det_permute, Equiv.Perm.sign_swap hij]
  simp
