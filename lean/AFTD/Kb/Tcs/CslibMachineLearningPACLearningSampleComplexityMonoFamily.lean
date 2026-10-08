import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningIsPACLearnerFor
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningSampleComplexity
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningSampleComplexityLeOfForall
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningIsPACLearnerForAntitoneFamily

/-!
# Cslib.MachineLearning.PACLearning.sampleComplexity_mono_family

Topic: learning   Node: 3144284a9afe

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.sampleComplexity_mono_family`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/Defs.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Deterministic sample complexity is monotone in the distribution family under `⊆`: a smaller family (fewer distributions to cover) requires no more samples.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal NNReal in
variable {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β] in
/-- Deterministic sample complexity is monotone in the distribution family under `⊆`: a smaller family (fewer distributions to cover) requires no more samples. -/
theorem Cslib.MachineLearning.PACLearning.sampleComplexity_mono_family {ε δ : Set.Ioo (0 : ℝ≥0) 1}
    {C : ConceptClass α β} {𝒟 𝒟' : Set (Measure (α × β))} (h𝒟 : 𝒟 ⊆ 𝒟')
    (h : ∃ m, IsPACLearnerFor m ε δ C 𝒟') :
    sampleComplexity IsPACLearnerFor C ε δ 𝒟 ≤ sampleComplexity IsPACLearnerFor C ε δ 𝒟' :=
  sampleComplexity_le_of_forall (fun h' => h'.antitone_family h𝒟) h
