import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningIsRPACLearnerFor
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningRsampleComplexity
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningSampleComplexityLeOfForall
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningIsRPACLearnerForAntitoneFamily

/-!
# Cslib.MachineLearning.PACLearning.rsampleComplexity_mono_family

Topic: learning   Node: 448103f23c6f

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.rsampleComplexity_mono_family`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/Defs.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Randomized sample complexity is monotone in the distribution family under `⊆`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal NNReal in
variable {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β] in
/-- Randomized sample complexity is monotone in the distribution family under `⊆`. -/
theorem Cslib.MachineLearning.PACLearning.rsampleComplexity_mono_family {ε δ : Set.Ioo (0 : ℝ≥0) 1}
    {C : ConceptClass α β} {𝒟 𝒟' : Set (Measure (α × β))} (h𝒟 : 𝒟 ⊆ 𝒟')
    (h : ∃ m, IsRPACLearnerFor.{_, _, 0} m ε δ C 𝒟') :
    rsampleComplexity C ε δ 𝒟 ≤ rsampleComplexity C ε δ 𝒟' :=
  sampleComplexity_le_of_forall (fun h' => h'.antitone_family h𝒟) h
