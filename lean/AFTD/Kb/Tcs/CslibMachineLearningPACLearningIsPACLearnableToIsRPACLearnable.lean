import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningIsPACLearnable
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningIsRPACLearnable
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningIsPACLearnerFor
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningIsRPACLearnerFor
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningIsPACLearnerForToIsRPACLearnerFor

/-!
# Cslib.MachineLearning.PACLearning.IsPACLearnable.toIsRPACLearnable

Topic: learning   Node: e5b6d6e9dbcc

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.IsPACLearnable.toIsRPACLearnable`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/Defs.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Deterministic PAC learnability implies randomized PAC learnability.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal NNReal in
variable {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β] in
/-- Deterministic PAC learnability implies randomized PAC learnability. -/
theorem Cslib.MachineLearning.PACLearning.IsPACLearnable.toIsRPACLearnable {C : ConceptClass α β}
    {𝒟 : Set (Measure (α × β))} (h : IsPACLearnable C 𝒟) :
    IsRPACLearnable C 𝒟 := by
  intro ε δ
  obtain ⟨m, hm⟩ := h ε δ
  exact ⟨m, hm.toIsRPACLearnerFor⟩
