import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapVariance
import AFTD.Kb.Physics.LinearPMapIsEigenvector
import AFTD.Kb.Physics.LinearPMapExpectedValue
import AFTD.Kb.Physics.LinearPMapVarianceEqZeroIff

/-!
# LinearPMap.variance_eq_zero_iff_isEigenvector

Topic: quantum_mechanics   Node: 0d23eb2d8124

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.variance_eq_zero_iff_isEigenvector`. Lean proof by Matteo Cipollina, Krystian Nowakowski, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/StateObservables/Variance.lean (Copyright (c) 2026 Axiomatic-AI. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For `‖ψ‖ = 1`, zero variance iff `ψ` is an eigenvector with eigenvalue `⟨T⟩_ψ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
open InnerProductSpace in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
/-- For `‖ψ‖ = 1`, zero variance iff `ψ` is an eigenvector with eigenvalue `⟨T⟩_ψ`. -/
lemma LinearPMap.variance_eq_zero_iff_isEigenvector (T : H →ₗ.[ℂ] H)
    (ψ : T.domain) (hψ_norm : ‖(ψ : H)‖ = 1) :
    variance T ψ = 0 ↔
      T.IsEigenvector ψ (expectedValue T ψ : ℂ) := by
  rw [variance_eq_zero_iff]
  constructor
  · intro h_centered
    refine ⟨h_centered, ?_⟩
    intro h_zero
    have h_zero' : (ψ : H) = 0 := by simpa using h_zero
    have h_norm_zero : ‖(ψ : H)‖ = 0 := by simp [h_zero']
    have : (0 : ℝ) = 1 := h_norm_zero.symm.trans hψ_norm
    norm_num at this
  · intro h_eigen
    exact h_eigen.1
