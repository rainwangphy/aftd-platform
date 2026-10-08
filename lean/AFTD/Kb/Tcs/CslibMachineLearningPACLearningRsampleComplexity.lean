import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningSampleComplexity
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningIsRPACLearnerFor

/-!
# Cslib.MachineLearning.PACLearning.rsampleComplexity

Topic: learning   Node: bf458acdf75f

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.rsampleComplexity`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/Defs.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The *randomized sample complexity* of `C`, i.e. `sampleComplexity` instantiated at the randomized learner model `IsRPACLearnerFor`. The randomness space is pinned to `Type 0`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal NNReal in
variable {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β] in
/-- The *randomized sample complexity* of `C`, i.e. `sampleComplexity` instantiated at the randomized learner model `IsRPACLearnerFor`. The randomness space is pinned to `Type 0`. -/
noncomputable def Cslib.MachineLearning.PACLearning.rsampleComplexity (C : ConceptClass α β) (ε δ : Set.Ioo (0 : ℝ≥0) 1)
    (𝒟 : Set (Measure (α × β))) : ℕ :=
  sampleComplexity IsRPACLearnerFor.{_, _, 0} C ε δ 𝒟
