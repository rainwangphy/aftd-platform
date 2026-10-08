import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningVersionSpaces
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningVersionSpacesSubsetPowerset

/-!
# Cslib.MachineLearning.PACLearning.versionSpaces_ncard_le

Topic: learning   Node: 38d4b9195c34

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.versionSpaces_ncard_le`. Lean proof by Dhruv Gupta, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/VersionSpaceLattice.lean (Copyright (c) 2026 Dhruv Gupta. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A finite concept class has at most `2 ^ C.ncard` version spaces: the lattice embeds in the powerset.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Set in
variable {α : Type*} {β : Type*} in
/-- A finite concept class has at most `2 ^ C.ncard` version spaces: the lattice embeds in the powerset. -/
theorem Cslib.MachineLearning.PACLearning.versionSpaces_ncard_le {C : ConceptClass α β} (hC : C.Finite) :
    (VersionSpaces C).ncard ≤ 2 ^ C.ncard :=
  (ncard_le_ncard (versionSpaces_subset_powerset C) hC.finite_subsets).trans_eq
    (ncard_powerset C hC)
