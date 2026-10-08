import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningVersionSpaces
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLabeledSample
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningVersionSpace
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningVersionSpaceSubset
import AFTD.Kb.Tcs.V

/-!
# Cslib.MachineLearning.PACLearning.versionSpaces_subset_powerset

Topic: learning   Node: 280d782d07b1

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.versionSpaces_subset_powerset`. Lean proof by Dhruv Gupta, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/VersionSpaceLattice.lean (Copyright (c) 2026 Dhruv Gupta. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Every version space is a subset of the class: the family lives in the powerset of `C`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Set in
variable {α : Type*} {β : Type*} in
/-- Every version space is a subset of the class: the family lives in the powerset of `C`. -/
theorem Cslib.MachineLearning.PACLearning.versionSpaces_subset_powerset (C : ConceptClass α β) :
    VersionSpaces C ⊆ 𝒫 C := by
  rintro V ⟨m, S, rfl⟩
  exact versionSpace_subset C S
