import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLabeledSample
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningRealizable
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningVersionSpace
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningMemVersionSpaceOfRealizable

/-!
# Cslib.MachineLearning.PACLearning.Realizable.versionSpace_nonempty

Topic: learning   Node: d1db42e7cd8e

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.Realizable.versionSpace_nonempty`. Lean proof by Dhruv Gupta, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/VersionSpace.lean (Copyright (c) 2026 Dhruv Gupta. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A realizable sample has nonempty version space.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal in
variable {α : Type*} {β : Type*} in
/-- A realizable sample has nonempty version space. -/
theorem Cslib.MachineLearning.PACLearning.Realizable.versionSpace_nonempty {m : ℕ} {C : ConceptClass α β}
    {S : LabeledSample α β m} (h : Realizable C S) :
    (VersionSpace C S).Nonempty :=
  ⟨h.choose, mem_versionSpace_of_realizable h.choose_spec.1 S h.choose_spec.2⟩
