import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapIsSymmetric
import AFTD.Kb.Physics.LinearPMapExpectedValue
import AFTD.Kb.Physics.LinearPMapConjInnerApplySelfEqOfIsSymmetric

/-!
# LinearPMap.expectedValue_eq_inner

Topic: quantum_mechanics   Node: b7aa95e60044

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.expectedValue_eq_inner`. Lean proof by Matteo Cipollina, Krystian Nowakowski, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/StateObservables/ExpectedValue.lean (Copyright (c) 2026 Axiomatic-AI. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If `T` is symmetric, `⟪ψ, Tψ⟫_ℂ` is the expectation value, coerced to `ℂ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
open InnerProductSpace in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
/-- If `T` is symmetric, `⟪ψ, Tψ⟫_ℂ` is the expectation value, coerced to `ℂ`. -/
lemma LinearPMap.expectedValue_eq_inner (T : H →ₗ.[ℂ] H) (hT : T.IsSymmetric) (ψ : T.domain) :
    ⟪(ψ : H), T ψ⟫_ℂ = (expectedValue T ψ : ℂ) := by
  have h_re : ((⟪(ψ : H), T ψ⟫_ℂ).re : ℂ) = ⟪(ψ : H), T ψ⟫_ℂ :=
    Complex.conj_eq_iff_re.mp
      (by simpa using conj_inner_apply_self_eq_of_isSymmetric T hT ψ)
  simpa [expectedValue] using h_re.symm
