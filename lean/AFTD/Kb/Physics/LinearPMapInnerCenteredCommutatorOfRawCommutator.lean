import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapIsSymmetric
import AFTD.Kb.Physics.LinearPMapRawCommutatorExpectation
import AFTD.Kb.Physics.LinearPMapCenteredCommutatorExpectation
import AFTD.Kb.Physics.LinearPMapExpectedValue
import AFTD.Kb.Physics.LinearPMapExpectedValueEqInner
import AFTD.Kb.Physics.LinearPMapCentered
import AFTD.Kb.Physics.LinearPMapSubExpectationCommutatorEqRaw
import AFTD.Kb.Physics.LinearPMapRawCommutatorEqOfSymmetric

/-!
# LinearPMap.inner_centered_commutator_of_raw_commutator

Topic: quantum_mechanics   Node: 6681211d1c4a

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.inner_centered_commutator_of_raw_commutator`. Lean proof by Matteo Cipollina, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Uncertainty.lean (Copyright (c) 2026 Axiomatic-AI. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A raw commutator expectation determines the centered commutator expectation.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
open InnerProductSpace in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
variable (A B : H →ₗ.[ℂ] H) (hA : A.IsSymmetric) (hB : B.IsSymmetric) in
variable (ψ : A.domain) in
variable (hψB : (ψ : H) ∈ B.domain) in
variable (hψ_norm : ‖(ψ : H)‖ = 1) in
variable (hBA : A ψ ∈ B.domain) in
variable (hAB : B ⟨ψ, hψB⟩ ∈ A.domain) in
variable {c : ℝ} in
variable (h_raw : rawCommutatorExpectation A B ψ hψB hBA hAB = Complex.I * c) in
include hA hB hψ_norm hBA hAB h_raw in
/-- A raw commutator expectation determines the centered commutator expectation. -/
lemma LinearPMap.inner_centered_commutator_of_raw_commutator :
    centeredCommutatorExpectation A B ψ hψB = Complex.I * c := by
  let a : H := A ψ
  let b : H := B ⟨ψ, hψB⟩
  let μa : ℝ := expectedValue A ψ
  let μb : ℝ := expectedValue B ⟨ψ, hψB⟩
  have hμa_right : ⟪(ψ : H), a⟫_ℂ = (μa : ℂ) := by
    simpa [a, μa] using expectedValue_eq_inner A hA ψ
  have hμa_left : ⟪a, (ψ : H)⟫_ℂ = (μa : ℂ) := by
    have h_symm : ⟪a, (ψ : H)⟫_ℂ = ⟪(ψ : H), a⟫_ℂ := by
      simpa [a] using hA ψ ψ
    simpa [h_symm] using hμa_right
  have hμb_right : ⟪(ψ : H), b⟫_ℂ = (μb : ℂ) := by
    simpa [b, μb] using expectedValue_eq_inner B hB ⟨ψ, hψB⟩
  have hμb_left : ⟪b, (ψ : H)⟫_ℂ = (μb : ℂ) := by
    have h_symm : ⟪b, (ψ : H)⟫_ℂ = ⟪(ψ : H), b⟫_ℂ := by
      simpa [b] using hB ⟨ψ, hψB⟩ ⟨ψ, hψB⟩
    simpa [h_symm] using hμb_right
  calc
    centeredCommutatorExpectation A B ψ hψB =
      ⟪centered A ψ, centered B ⟨ψ, hψB⟩⟫_ℂ -
        ⟪centered B ⟨ψ, hψB⟩, centered A ψ⟫_ℂ := by
          rfl
    _ =
      ⟪a - (μa : ℂ) • (ψ : H), b - (μb : ℂ) • (ψ : H)⟫_ℂ -
        ⟪b - (μb : ℂ) • (ψ : H), a - (μa : ℂ) • (ψ : H)⟫_ℂ := by
          rfl
    _ = ⟪a, b⟫_ℂ - ⟪b, a⟫_ℂ :=
      sub_expectation_commutator_eq_raw (ψ : H) a b μa μb
        hμa_right hμa_left hμb_right hμb_left hψ_norm
    _ = Complex.I * c :=
      raw_commutator_eq_of_symmetric A B hA hB ψ hψB hBA hAB
        (by simpa [rawCommutatorExpectation] using h_raw)
