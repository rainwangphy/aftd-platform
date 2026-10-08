import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningIsPACLearnable
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningSampleComplexity
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningIsPACLearnerFor
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningSampleComplexityLeOfForall
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningIsPACLearnerForMonoEpsilon

/-!
# Cslib.MachineLearning.PACLearning.IsPACLearnable.sampleComplexity_antitone_ε

Topic: learning   Node: eb64cec837b0

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.IsPACLearnable.sampleComplexity_antitone_ε`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/Defs.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`sampleComplexity_antitone_ε` for a learnable class.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal NNReal in
variable {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β] in
/-- `sampleComplexity_antitone_ε` for a learnable class. -/
theorem Cslib.MachineLearning.PACLearning.IsPACLearnable.sampleComplexity_antitone_ε
    {C : ConceptClass α β} {𝒟 : Set (Measure (α × β))} (hL : IsPACLearnable C 𝒟)
    {ε₁ ε₂ δ : Set.Ioo (0 : ℝ≥0) 1} (hε : ε₁.val ≤ ε₂.val) :
    sampleComplexity IsPACLearnerFor C ε₂ δ 𝒟 ≤ sampleComplexity IsPACLearnerFor C ε₁ δ 𝒟 :=
  sampleComplexity_le_of_forall (fun h' => h'.mono_ε hε) (hL ε₁ δ)
