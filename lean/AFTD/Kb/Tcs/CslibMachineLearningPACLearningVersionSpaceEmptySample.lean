import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLabeledSample
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningVersionSpace

/-!
# Cslib.MachineLearning.PACLearning.versionSpace_empty_sample

Topic: learning   Node: 0cdfeddf9c97

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.versionSpace_empty_sample`. Lean proof by Dhruv Gupta, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/VersionSpace.lean (Copyright (c) 2026 Dhruv Gupta. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Version space on the empty sample equals the whole concept class.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal in
variable {α : Type*} {β : Type*} in
/-- Version space on the empty sample equals the whole concept class. -/
theorem Cslib.MachineLearning.PACLearning.versionSpace_empty_sample (C : ConceptClass α β)
    (S : LabeledSample α β 0) :
    VersionSpace C S = C := by
  ext h
  exact ⟨fun hh => hh.1, fun hh => ⟨hh, fun i => i.elim0⟩⟩
