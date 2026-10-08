import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLabeledSample
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningVersionSpace
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningVersionSpaceReindex

/-!
# Cslib.MachineLearning.PACLearning.versionSpace_antitone

Topic: learning   Node: 5688747cf091

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.versionSpace_antitone`. Lean proof by Dhruv Gupta, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/VersionSpace.lean (Copyright (c) 2026 Dhruv Gupta. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

*Version space antitonicity.* Given a sample of size `n` and `m ≤ n`, the version space on all `n` observations is a subset of the version space on the first `m` observations. Special case of `versionSpace_reindex` with `f := Fin.castLE hmn`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal in
variable {α : Type*} {β : Type*} in
/-- *Version space antitonicity.* Given a sample of size `n` and `m ≤ n`, the version space on all `n` observations is a subset of the version space on the first `m` observations. Special case of `versionSpace_reindex` with `f := Fin.castLE hmn`. -/
theorem Cslib.MachineLearning.PACLearning.versionSpace_antitone {m n : ℕ} (hmn : m ≤ n) (C : ConceptClass α β)
    (S : LabeledSample α β n) :
    VersionSpace C S ⊆ VersionSpace C (S ∘ Fin.castLE hmn) :=
  versionSpace_reindex (Fin.castLE hmn) C S
