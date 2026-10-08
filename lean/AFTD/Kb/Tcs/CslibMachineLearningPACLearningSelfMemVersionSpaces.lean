import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningVersionSpaces
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLabeledSample
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningVersionSpace
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningVersionSpaceEmptySample

/-!
# Cslib.MachineLearning.PACLearning.self_mem_versionSpaces

Topic: learning   Node: d51cc71b4a5c

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.self_mem_versionSpaces`. Lean proof by Dhruv Gupta, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/VersionSpaceLattice.lean (Copyright (c) 2026 Dhruv Gupta. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The whole class is a version space (of the empty sample) which means the family has top `C`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Set in
variable {α : Type*} {β : Type*} in
/-- The whole class is a version space (of the empty sample) which means the family has top `C`. -/
theorem Cslib.MachineLearning.PACLearning.self_mem_versionSpaces (C : ConceptClass α β) : C ∈ VersionSpaces C :=
  ⟨0, Fin.elim0, (versionSpace_empty_sample C Fin.elim0).symm⟩
