import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLabeledSample
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningVersionSpace
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningEmpiricalMiscount

/-!
# Cslib.MachineLearning.PACLearning.mem_versionSpace_iff_empiricalMiscount_zero

Topic: learning   Node: 23f0703c0575

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.mem_versionSpace_iff_empiricalMiscount_zero`. Lean proof by Dhruv Gupta, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/VersionSpace.lean (Copyright (c) 2026 Dhruv Gupta. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Version-space membership equals concept-class membership plus zero empirical miscount (combinatorial bridge).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal in
variable {α : Type*} {β : Type*} in
/-- Version-space membership equals concept-class membership plus zero empirical miscount (combinatorial bridge). -/
theorem Cslib.MachineLearning.PACLearning.mem_versionSpace_iff_empiricalMiscount_zero [DecidableEq β]
    {m : ℕ} {C : ConceptClass α β} {S : LabeledSample α β m} {h : α → β} :
    h ∈ VersionSpace C S ↔ h ∈ C ∧ empiricalMiscount h S = 0 := by
  simp only [empiricalMiscount, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
             Finset.mem_univ, true_implies, ne_eq, Decidable.not_not]
  rfl
