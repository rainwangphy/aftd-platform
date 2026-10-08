import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningIsRPACLearnerFor
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLearner
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLabeledSample
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningError
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningOptimalError

/-!
# Cslib.MachineLearning.PACLearning.IsRPACLearnerFor.mono_δ

Topic: learning   Node: 5c0593ca6b7f

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.IsRPACLearnerFor.mono_δ`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/Defs.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A randomized PAC learner with confidence `δ₁` is also a randomized PAC learner with any weaker confidence `δ₂ ≥ δ₁`. Unlike `mono_ε` or `antitone_C`, this does not touch the integrand, so it carries the `AEMeasurable` part through unchanged.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal NNReal in
variable {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β] in
/-- A randomized PAC learner with confidence `δ₁` is also a randomized PAC learner with any weaker confidence `δ₂ ≥ δ₁`. Unlike `mono_ε` or `antitone_C`, this does not touch the integrand, so it carries the `AEMeasurable` part through unchanged. -/
theorem Cslib.MachineLearning.PACLearning.IsRPACLearnerFor.mono_δ.{u} {m : ℕ} {ε : Set.Ioo (0 : ℝ≥0) 1}
    {δ₁ δ₂ : Set.Ioo (0 : ℝ≥0) 1} (hδ : δ₁.val ≤ δ₂.val)
    {C : ConceptClass α β} {𝒟 : Set (Measure (α × β))}
    (h : IsRPACLearnerFor.{_, _, u} m ε δ₁ C 𝒟) :
    IsRPACLearnerFor.{_, _, u} m ε δ₂ C 𝒟 := by
  obtain ⟨Ω, mΩ, Q, hQ, A, hA⟩ := h
  refine ⟨Ω, mΩ, Q, hQ, A, fun D inst hD => ?_⟩
  obtain ⟨hmeas, hint⟩ := @hA D inst hD
  refine ⟨hmeas, le_trans hint ?_⟩
  exact_mod_cast hδ
