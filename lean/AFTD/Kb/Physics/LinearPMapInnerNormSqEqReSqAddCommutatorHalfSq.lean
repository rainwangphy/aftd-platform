import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapInnerImOfCommutatorEq

/-!
# LinearPMap.inner_norm_sq_eq_re_sq_add_commutator_half_sq

Topic: quantum_mechanics   Node: a84efee85b9c

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.inner_norm_sq_eq_re_sq_add_commutator_half_sq`. Lean proof by Matteo Cipollina, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Uncertainty.lean (Copyright (c) 2026 Axiomatic-AI. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.inner_norm_sq_eq_re_sq_add_commutator_half_sq
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
open InnerProductSpace in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
lemma LinearPMap.inner_norm_sq_eq_re_sq_add_commutator_half_sq {u v : H} {c : ℝ}
    (h_comm : ⟪u, v⟫_ℂ - ⟪v, u⟫_ℂ = Complex.I * c) :
    ‖⟪u, v⟫_ℂ‖ ^ 2 = (⟪u, v⟫_ℂ).re ^ 2 + (c / 2) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, inner_im_of_commutator_eq h_comm]
  ring
