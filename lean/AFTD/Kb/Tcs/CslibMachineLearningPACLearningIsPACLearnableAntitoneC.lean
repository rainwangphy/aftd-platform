import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningIsPACLearnable
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningIsPACLearnerFor
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningIsPACLearnerForAntitoneC

/-!
# Cslib.MachineLearning.PACLearning.IsPACLearnable.antitone_C

Topic: learning   Node: 0cad7d4ea26e

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.IsPACLearnable.antitone_C`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/Defs.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

PAC learnability is antitone in the concept class: a subclass of a learnable class is learnable.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal NNReal in
variable {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β] in
/-- PAC learnability is antitone in the concept class: a subclass of a learnable class is learnable. -/
theorem Cslib.MachineLearning.PACLearning.IsPACLearnable.antitone_C {C C' : ConceptClass α β} (hC : C ⊆ C')
    {𝒟 : Set (Measure (α × β))} (h : IsPACLearnable C' 𝒟) : IsPACLearnable C 𝒟 :=
  fun ε δ => (h ε δ).imp fun _ hm => hm.antitone_C hC
