import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLabeledSample
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningVersionSpace

/-!
# Cslib.MachineLearning.PACLearning.mem_versionSpace_iff

Topic: learning   Node: 50a7730389ba

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.mem_versionSpace_iff`. Lean proof by Dhruv Gupta, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/VersionSpace.lean (Copyright (c) 2026 Dhruv Gupta. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Membership in the version space unfolds to concept membership plus per-sample consistency.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal in
variable {α : Type*} {β : Type*} in
/-- Membership in the version space unfolds to concept membership plus per-sample consistency. -/
theorem Cslib.MachineLearning.PACLearning.mem_versionSpace_iff {m : ℕ} {C : ConceptClass α β}
    {S : LabeledSample α β m} {h : α → β} :
    h ∈ VersionSpace C S ↔ h ∈ C ∧ ∀ i : Fin m, h (S i).1 = (S i).2 := Iff.rfl
