import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningIsRPACLearnable
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningIsRPACLearnerFor
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningIsRPACLearnerForAntitoneFamily

/-!
# Cslib.MachineLearning.PACLearning.IsRPACLearnable.antitone_family

Topic: learning   Node: af797211b939

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.IsRPACLearnable.antitone_family`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/Defs.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Randomized PAC learnability is antitone in the distribution family.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal NNReal in
variable {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β] in
/-- Randomized PAC learnability is antitone in the distribution family. -/
theorem Cslib.MachineLearning.PACLearning.IsRPACLearnable.antitone_family {C : ConceptClass α β}
    {𝒟 𝒟' : Set (Measure (α × β))} (h𝒟 : 𝒟 ⊆ 𝒟')
    (h : IsRPACLearnable C 𝒟') : IsRPACLearnable C 𝒟 :=
  fun ε δ => (h ε δ).imp fun _ hm => hm.antitone_family h𝒟
