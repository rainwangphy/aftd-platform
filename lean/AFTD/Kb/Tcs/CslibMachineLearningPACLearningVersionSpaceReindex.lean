import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLabeledSample
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningVersionSpace

/-!
# Cslib.MachineLearning.PACLearning.versionSpace_reindex

Topic: learning   Node: 47af07423065

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.versionSpace_reindex`. Lean proof by Dhruv Gupta, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/VersionSpace.lean (Copyright (c) 2026 Dhruv Gupta. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

*Version space reindexing.* For any reindexing `f : Fin m → Fin n`, the version space on `S` is contained in the version space on the reindexed sample `S ∘ f`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal in
variable {α : Type*} {β : Type*} in
/-- *Version space reindexing.* For any reindexing `f : Fin m → Fin n`, the version space on `S` is contained in the version space on the reindexed sample `S ∘ f`. -/
theorem Cslib.MachineLearning.PACLearning.versionSpace_reindex {m n : ℕ} (f : Fin m → Fin n) (C : ConceptClass α β)
    (S : LabeledSample α β n) :
    VersionSpace C S ⊆ VersionSpace C (S ∘ f) :=
  fun _ hh => ⟨hh.1, fun i => hh.2 (f i)⟩
