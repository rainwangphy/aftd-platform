import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningIsPACLearnable
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningSampleComplexity
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningIsPACLearnerFor
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningSampleComplexityLeOfForall
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningIsPACLearnerForMonoDelta

/-!
# Cslib.MachineLearning.PACLearning.IsPACLearnable.sampleComplexity_antitone_δ

Topic: learning   Node: e359a850614c

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.IsPACLearnable.sampleComplexity_antitone_δ`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/Defs.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`sampleComplexity_antitone_δ` for a learnable class: the nonemptiness hypothesis comes for free from `IsPACLearnable`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal NNReal in
variable {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β] in
/-- `sampleComplexity_antitone_δ` for a learnable class: the nonemptiness hypothesis comes for free from `IsPACLearnable`. -/
theorem Cslib.MachineLearning.PACLearning.IsPACLearnable.sampleComplexity_antitone_δ
    {C : ConceptClass α β} {𝒟 : Set (Measure (α × β))} (hL : IsPACLearnable C 𝒟)
    {ε δ₁ δ₂ : Set.Ioo (0 : ℝ≥0) 1} (hδ : δ₁.val ≤ δ₂.val) :
    sampleComplexity IsPACLearnerFor C ε δ₂ 𝒟 ≤ sampleComplexity IsPACLearnerFor C ε δ₁ 𝒟 :=
  sampleComplexity_le_of_forall (fun h' => h'.mono_δ hδ) (hL ε δ₁)
