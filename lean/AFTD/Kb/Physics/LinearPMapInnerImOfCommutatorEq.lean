import AFTD.Prelude

/-!
# LinearPMap.inner_im_of_commutator_eq

Topic: quantum_mechanics   Node: 7f3261947693

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.inner_im_of_commutator_eq`. Lean proof by Matteo Cipollina, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Uncertainty.lean (Copyright (c) 2026 Axiomatic-AI. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.inner_im_of_commutator_eq
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open InnerProductSpace in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
lemma LinearPMap.inner_im_of_commutator_eq {u v : H} {c : ℝ}
    (h_comm : ⟪u, v⟫_ℂ - ⟪v, u⟫_ℂ = Complex.I * c) :
    (⟪u, v⟫_ℂ).im = c / 2 := by
  have h_conj_im : (⟪v, u⟫_ℂ).im = -(⟪u, v⟫_ℂ).im := by
    rw [(inner_conj_symm (𝕜 := ℂ) v u).symm, Complex.conj_im]
  have h_im := congrArg Complex.im h_comm
  rw [Complex.sub_im] at h_im
  simp at h_im
  rw [h_conj_im] at h_im
  linarith
