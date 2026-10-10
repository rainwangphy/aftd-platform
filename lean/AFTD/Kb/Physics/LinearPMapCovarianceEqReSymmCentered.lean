import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapCovariance
import AFTD.Kb.Physics.LinearPMapCentered
import AFTD.Kb.Physics.LinearPMapCovarianceEqReInnerCentered

/-!
# LinearPMap.covariance_eq_re_symm_centered

Topic: quantum_mechanics   Node: 48ff98119e69

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.covariance_eq_re_symm_centered`. Lean proof by Matteo Cipollina, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Covariance.lean (Copyright (c) 2026 Axiomatic-AI. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Covariance as the real part of the symmetrized centered inner product.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
open InnerProductSpace in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
variable (A B : H →ₗ.[ℂ] H) in
variable (ψ : A.domain) in
variable (hψB : (ψ : H) ∈ B.domain) in
/-- Covariance as the real part of the symmetrized centered inner product. -/
lemma LinearPMap.covariance_eq_re_symm_centered :
    covariance A B ψ hψB =
      ((⟪centered A ψ, centered B ⟨ψ, hψB⟩⟫_ℂ +
        ⟪centered B ⟨ψ, hψB⟩, centered A ψ⟫_ℂ).re) / 2 := by
  let z : ℂ := ⟪centered A ψ, centered B ⟨ψ, hψB⟩⟫_ℂ
  have hz : ⟪centered B ⟨ψ, hψB⟩, centered A ψ⟫_ℂ = star z := by
    simp [z, inner_conj_symm]
  rw [covariance_eq_re_inner_centered, hz]
  change z.re = ((z + star z).re) / 2
  simp only [Complex.add_re, Complex.star_def, Complex.conj_re, add_self_div_two]
