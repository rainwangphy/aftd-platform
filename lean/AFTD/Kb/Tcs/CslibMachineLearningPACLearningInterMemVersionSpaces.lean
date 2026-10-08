import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLabeledSample
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningVersionSpaces
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningVersionSpace
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningVersionSpaceAppend

/-!
# Cslib.MachineLearning.PACLearning.inter_mem_versionSpaces

Topic: learning   Node: aee9196ce00a

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.inter_mem_versionSpaces`. Lean proof by Dhruv Gupta, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/VersionSpaceLattice.lean (Copyright (c) 2026 Dhruv Gupta. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The version-space family is closed under intersection (append the witnessing samples).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Set in
variable {α : Type*} {β : Type*} in
/-- The version-space family is closed under intersection (append the witnessing samples). -/
theorem Cslib.MachineLearning.PACLearning.inter_mem_versionSpaces {C U V : ConceptClass α β}
    (hU : U ∈ VersionSpaces C) (hV : V ∈ VersionSpaces C) :
    U ∩ V ∈ VersionSpaces C := by
  obtain ⟨m, S, rfl⟩ := hU
  obtain ⟨n, T, rfl⟩ := hV
  exact ⟨m + n, Fin.append S T, (versionSpace_append C S T).symm⟩
