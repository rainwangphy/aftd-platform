import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapInnerImOfCommutatorEq

/-!
# LinearPMap.commutator_half_sq_le_mul_norm_sq

Topic: quantum_mechanics   Node: 18cba502433a

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.commutator_half_sq_le_mul_norm_sq`. Lean proof by Matteo Cipollina, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Uncertainty.lean (Copyright (c) 2026 Axiomatic-AI. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.commutator_half_sq_le_mul_norm_sq
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
open InnerProductSpace in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
lemma LinearPMap.commutator_half_sq_le_mul_norm_sq {u v : H} {c : ℝ}
    (h_comm : ⟪u, v⟫_ℂ - ⟪v, u⟫_ℂ = Complex.I * c) :
    (|c| / 2) ^ 2 ≤ (‖u‖ * ‖v‖) ^ 2 := by
  suffices (|c| / 2) ^ 2 ≤ (‖u‖ * ‖v‖) ^ 2 by exact this
  have h_sq : |c / 2| ^ 2 ≤ (‖u‖ * ‖v‖) ^ 2 := by
    have h_bound : |c / 2| ≤ ‖u‖ * ‖v‖ := by
      have h_im : |(⟪u, v⟫_ℂ).im| ≤ ‖u‖ * ‖v‖ :=
        le_trans (Complex.abs_im_le_norm ⟪u, v⟫_ℂ) (norm_inner_le_norm u v)
      rwa [inner_im_of_commutator_eq h_comm] at h_im
    have h_nonneg : 0 ≤ ‖u‖ * ‖v‖ := mul_nonneg (norm_nonneg u) (norm_nonneg v)
    nlinarith [abs_nonneg (c / 2), h_bound, h_nonneg]
  simpa [abs_div] using h_sq
