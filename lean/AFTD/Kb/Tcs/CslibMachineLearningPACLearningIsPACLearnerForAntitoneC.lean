import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningIsPACLearnerFor
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLearner
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLabeledSample
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningError
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningOptimalError

/-!
# Cslib.MachineLearning.PACLearning.IsPACLearnerFor.antitone_C

Topic: learning   Node: ef671fb093fe

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.IsPACLearnerFor.antitone_C`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/Defs.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The deterministic PAC learner predicate is antitone in the concept class: a learner for a larger class `C'` is also a learner for any subclass `C ⊆ C'`, since the agnostic benchmark `optimalError _ C ≥ optimalError _ C'` makes the error requirement easier.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal NNReal in
variable {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β] in
/-- The deterministic PAC learner predicate is antitone in the concept class: a learner for a larger class `C'` is also a learner for any subclass `C ⊆ C'`, since the agnostic benchmark `optimalError _ C ≥ optimalError _ C'` makes the error requirement easier. -/
theorem Cslib.MachineLearning.PACLearning.IsPACLearnerFor.antitone_C {m : ℕ} {ε δ : Set.Ioo (0 : ℝ≥0) 1}
    {C C' : ConceptClass α β} (hC : C ⊆ C')
    {𝒟 : Set (Measure (α × β))} (h : IsPACLearnerFor m ε δ C' 𝒟) :
    IsPACLearnerFor m ε δ C 𝒟 := by
  obtain ⟨A, hA⟩ := h
  refine ⟨A, fun D inst hD => le_trans (measure_mono ?_) (@hA D inst hD)⟩
  intro S hS
  have h_opt : optimalError D C' ≤ optimalError D C := iInf_le_iInf_of_subset hC
  calc optimalError D C' + (↑ε.val : ℝ≥0∞)
      ≤ optimalError D C + ↑ε.val := by gcongr
    _ < error D (A S) := hS
