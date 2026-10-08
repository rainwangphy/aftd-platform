import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningVersionSpaces
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLabeledSample
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningVersionSpace
import AFTD.Kb.Tcs.V

/-!
# Cslib.MachineLearning.PACLearning.mem_versionSpaces_iff

Topic: learning   Node: 0eba6a51da21

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.mem_versionSpaces_iff`. Lean proof by Dhruv Gupta, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/VersionSpaceLattice.lean (Copyright (c) 2026 Dhruv Gupta. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Membership in the version-space family unfolds to a witnessing sample.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Set in
variable {α : Type*} {β : Type*} in
/-- Membership in the version-space family unfolds to a witnessing sample. -/
theorem Cslib.MachineLearning.PACLearning.mem_versionSpaces_iff {C V : ConceptClass α β} :
    V ∈ VersionSpaces C ↔ ∃ (m : ℕ) (S : LabeledSample α β m), V = VersionSpace C S :=
  Iff.rfl
