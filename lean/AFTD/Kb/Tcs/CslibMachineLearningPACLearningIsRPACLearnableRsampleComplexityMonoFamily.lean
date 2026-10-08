import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningIsRPACLearnable
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningRsampleComplexity
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningSampleComplexityLeOfForall
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningIsRPACLearnerFor
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningIsRPACLearnerForAntitoneFamily

/-!
# Cslib.MachineLearning.PACLearning.IsRPACLearnable.rsampleComplexity_mono_family

Topic: learning   Node: 111d2901b4f6

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.IsRPACLearnable.rsampleComplexity_mono_family`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/Defs.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`rsampleComplexity_mono_family` for a randomized-learnable class.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal NNReal in
variable {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β] in
/-- `rsampleComplexity_mono_family` for a randomized-learnable class. -/
theorem Cslib.MachineLearning.PACLearning.IsRPACLearnable.rsampleComplexity_mono_family
    {C : ConceptClass α β} {𝒟 𝒟' : Set (Measure (α × β))}
    (hL : IsRPACLearnable C 𝒟') (h𝒟 : 𝒟 ⊆ 𝒟') {ε δ : Set.Ioo (0 : ℝ≥0) 1} :
    rsampleComplexity C ε δ 𝒟 ≤ rsampleComplexity C ε δ 𝒟' :=
  sampleComplexity_le_of_forall (fun h' => h'.antitone_family h𝒟) (hL ε δ)
