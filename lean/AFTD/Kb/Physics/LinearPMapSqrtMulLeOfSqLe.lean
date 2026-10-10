import AFTD.Prelude

/-!
# LinearPMap.sqrt_mul_le_of_sq_le

Topic: quantum_mechanics   Node: 04223b1fb30e

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.sqrt_mul_le_of_sq_le`. Lean proof by Matteo Cipollina, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Uncertainty.lean (Copyright (c) 2026 Axiomatic-AI. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.sqrt_mul_le_of_sq_le
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open InnerProductSpace in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
lemma LinearPMap.sqrt_mul_le_of_sq_le {x y z : ℝ}
    (hx : 0 ≤ x) (hz : 0 ≤ z) (hxy : z ^ 2 ≤ x * y) :
    z ≤ Real.sqrt x * Real.sqrt y := by
  suffices z ≤ Real.sqrt x * Real.sqrt y by exact this
  have hs : Real.sqrt (z ^ 2) ≤ Real.sqrt (x * y) := Real.sqrt_le_sqrt hxy
  rw [Real.sqrt_sq hz, Real.sqrt_mul hx] at hs
  simpa [mul_comm] using hs
