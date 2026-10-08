import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningIsPACLearnerFor
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLearner
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLabeledSample
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningError
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningOptimalError

/-!
# Cslib.MachineLearning.PACLearning.IsPACLearnerFor.mono_ε

Topic: learning   Node: a360b57f3e80

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.IsPACLearnerFor.mono_ε`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/Defs.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A PAC learner with accuracy `ε₁` is also a PAC learner with any weaker accuracy `ε₂ ≥ ε₁`: the bad event `{error > opt + ε}` only shrinks.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal NNReal in
variable {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β] in
/-- A PAC learner with accuracy `ε₁` is also a PAC learner with any weaker accuracy `ε₂ ≥ ε₁`: the bad event `{error > opt + ε}` only shrinks. -/
theorem Cslib.MachineLearning.PACLearning.IsPACLearnerFor.mono_ε {m : ℕ} {δ : Set.Ioo (0 : ℝ≥0) 1}
    {ε₁ ε₂ : Set.Ioo (0 : ℝ≥0) 1} (hε : ε₁.val ≤ ε₂.val)
    {C : ConceptClass α β} {𝒟 : Set (Measure (α × β))}
    (h : IsPACLearnerFor m ε₁ δ C 𝒟) :
    IsPACLearnerFor m ε₂ δ C 𝒟 := by
  obtain ⟨A, hA⟩ := h
  refine ⟨A, fun D inst hD => le_trans (measure_mono ?_) (@hA D inst hD)⟩
  intro S hS
  have hε' : (↑ε₁.val : ℝ≥0∞) ≤ ↑ε₂.val := by exact_mod_cast hε
  calc optimalError D C + (↑ε₁.val : ℝ≥0∞)
      ≤ optimalError D C + ↑ε₂.val := by gcongr
    _ < error D (A S) := hS
