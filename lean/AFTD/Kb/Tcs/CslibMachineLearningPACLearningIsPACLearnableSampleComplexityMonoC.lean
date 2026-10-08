import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningIsPACLearnable
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningSampleComplexity
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningIsPACLearnerFor
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningSampleComplexityLeOfForall
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningIsPACLearnerForAntitoneC

/-!
# Cslib.MachineLearning.PACLearning.IsPACLearnable.sampleComplexity_mono_C

Topic: learning   Node: b0222c7a00c6

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.IsPACLearnable.sampleComplexity_mono_C`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/Defs.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`sampleComplexity_mono_C` for a learnable class (learnability at the *larger* class `C'` is the hypothesis).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal NNReal in
variable {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β] in
/-- `sampleComplexity_mono_C` for a learnable class (learnability at the *larger* class `C'` is the hypothesis). -/
theorem Cslib.MachineLearning.PACLearning.IsPACLearnable.sampleComplexity_mono_C
    {C C' : ConceptClass α β} {𝒟 : Set (Measure (α × β))}
    (hL : IsPACLearnable C' 𝒟) (hC : C ⊆ C') {ε δ : Set.Ioo (0 : ℝ≥0) 1} :
    sampleComplexity IsPACLearnerFor C ε δ 𝒟 ≤ sampleComplexity IsPACLearnerFor C' ε δ 𝒟 :=
  sampleComplexity_le_of_forall (fun h' => h'.antitone_C hC) (hL ε δ)
