import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLabeledSample
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningVersionSpace

/-!
# Cslib.MachineLearning.PACLearning.versionSpace_subset

Topic: learning   Node: d13f62c29a51

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.versionSpace_subset`. Lean proof by Dhruv Gupta, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/VersionSpace.lean (Copyright (c) 2026 Dhruv Gupta. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The version space is a subset of the original concept class.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal in
variable {α : Type*} {β : Type*} in
/-- The version space is a subset of the original concept class. -/
theorem Cslib.MachineLearning.PACLearning.versionSpace_subset {m : ℕ} (C : ConceptClass α β)
    (S : LabeledSample α β m) :
    VersionSpace C S ⊆ C := fun _ hh => hh.1
