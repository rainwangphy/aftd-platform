import AFTD.Prelude

/-!
# LinearPMap.sub_expectation_commutator_eq_raw

Topic: quantum_mechanics   Node: 75c0681e610f

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.sub_expectation_commutator_eq_raw`. Lean proof by Matteo Cipollina, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Uncertainty.lean (Copyright (c) 2026 Axiomatic-AI. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.sub_expectation_commutator_eq_raw
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open InnerProductSpace in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
lemma LinearPMap.sub_expectation_commutator_eq_raw
    (ψ a b : H) (μa μb : ℝ)
    (hμa_right : ⟪ψ, a⟫_ℂ = (μa : ℂ)) (hμa_left : ⟪a, ψ⟫_ℂ = (μa : ℂ))
    (hμb_right : ⟪ψ, b⟫_ℂ = (μb : ℂ)) (hμb_left : ⟪b, ψ⟫_ℂ = (μb : ℂ)) (hψ_norm : ‖ψ‖ = 1) :
    ⟪a - (μa : ℂ) • ψ, b - (μb : ℂ) • ψ⟫_ℂ -
        ⟪b - (μb : ℂ) • ψ, a - (μa : ℂ) • ψ⟫_ℂ =
      ⟪a, b⟫_ℂ - ⟪b, a⟫_ℂ := by
  calc
    ⟪a - (μa : ℂ) • ψ, b - (μb : ℂ) • ψ⟫_ℂ -
        ⟪b - (μb : ℂ) • ψ, a - (μa : ℂ) • ψ⟫_ℂ =
          (⟪a, b⟫_ℂ - (μb : ℂ) * ⟪a, ψ⟫_ℂ - star (μa : ℂ) * ⟪ψ, b⟫_ℂ +
            star (μa : ℂ) * (μb : ℂ) * ⟪ψ, ψ⟫_ℂ) -
          (⟪b, a⟫_ℂ - (μa : ℂ) * ⟪b, ψ⟫_ℂ - star (μb : ℂ) * ⟪ψ, a⟫_ℂ +
            star (μb : ℂ) * (μa : ℂ) * ⟪ψ, ψ⟫_ℂ) := by
              simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
              simp [mul_comm, mul_assoc]
              ring_nf
    _ = ⟪a, b⟫_ℂ - ⟪b, a⟫_ℂ := by
          rw [hμa_right, hμa_left, hμb_right, hμb_left, inner_self_eq_norm_sq_to_K,
            hψ_norm]
          simp only [Complex.star_def, Complex.conj_ofReal, pow_two, mul_assoc, mul_comm]
          ring_nf
