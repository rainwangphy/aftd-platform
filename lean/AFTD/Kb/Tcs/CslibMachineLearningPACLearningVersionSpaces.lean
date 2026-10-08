import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLabeledSample
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningVersionSpace
import AFTD.Kb.Tcs.V

/-!
# Cslib.MachineLearning.PACLearning.VersionSpaces

Topic: learning   Node: 1eb0b0de5b07

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.VersionSpaces`. Lean proof by Dhruv Gupta, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/VersionSpaceLattice.lean (Copyright (c) 2026 Dhruv Gupta. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The family of all version spaces of a concept class, over labeled samples of every size.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Set in
variable {α : Type*} {β : Type*} in
/-- The family of all version spaces of a concept class, over labeled samples of every size. -/
def Cslib.MachineLearning.PACLearning.VersionSpaces (C : ConceptClass α β) : Set (ConceptClass α β) :=
  {V | ∃ (m : ℕ) (S : LabeledSample α β m), V = VersionSpace C S}
