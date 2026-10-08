import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningIsPACLearnerFor
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningSampleComplexity
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningSampleComplexityLeOfForall
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningIsPACLearnerForMonoDelta

/-!
# Cslib.MachineLearning.PACLearning.sampleComplexity_antitone_δ

Topic: learning   Node: 20e40d02cf5b

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.sampleComplexity_antitone_δ`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/Defs.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Deterministic sample complexity is antitone in the confidence parameter `δ`: weaker confidence requires no more samples.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal NNReal in
variable {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β] in
/-- Deterministic sample complexity is antitone in the confidence parameter `δ`: weaker confidence requires no more samples. -/
theorem Cslib.MachineLearning.PACLearning.sampleComplexity_antitone_δ {ε δ₁ δ₂ : Set.Ioo (0 : ℝ≥0) 1} (hδ : δ₁.val ≤ δ₂.val)
    {C : ConceptClass α β} {𝒟 : Set (Measure (α × β))}
    (h : ∃ m, IsPACLearnerFor m ε δ₁ C 𝒟) :
    sampleComplexity IsPACLearnerFor C ε δ₂ 𝒟 ≤ sampleComplexity IsPACLearnerFor C ε δ₁ 𝒟 :=
  sampleComplexity_le_of_forall (fun h' => h'.mono_δ hδ) h
