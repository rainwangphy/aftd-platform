import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningIsPACLearnerFor
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLearner
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLabeledSample
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningError
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningOptimalError

/-!
# Cslib.MachineLearning.PACLearning.IsPACLearnerFor.mono_δ

Topic: learning   Node: 811862340935

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.IsPACLearnerFor.mono_δ`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/Defs.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A PAC learner with confidence `δ₁` is also a PAC learner with any weaker confidence `δ₂ ≥ δ₁`: the failure-probability bound only gets looser.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal NNReal in
variable {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β] in
/-- A PAC learner with confidence `δ₁` is also a PAC learner with any weaker confidence `δ₂ ≥ δ₁`: the failure-probability bound only gets looser. -/
theorem Cslib.MachineLearning.PACLearning.IsPACLearnerFor.mono_δ {m : ℕ} {ε : Set.Ioo (0 : ℝ≥0) 1}
    {δ₁ δ₂ : Set.Ioo (0 : ℝ≥0) 1} (hδ : δ₁.val ≤ δ₂.val)
    {C : ConceptClass α β} {𝒟 : Set (Measure (α × β))}
    (h : IsPACLearnerFor m ε δ₁ C 𝒟) :
    IsPACLearnerFor m ε δ₂ C 𝒟 := by
  obtain ⟨A, hA⟩ := h
  refine ⟨A, fun D inst hD => le_trans (@hA D inst hD) ?_⟩
  exact_mod_cast hδ
