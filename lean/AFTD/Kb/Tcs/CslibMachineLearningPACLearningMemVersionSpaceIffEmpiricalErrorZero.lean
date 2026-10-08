import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLabeledSample
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningVersionSpace
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningEmpiricalError
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningError
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningEmpiricalMeasure

/-!
# Cslib.MachineLearning.PACLearning.mem_versionSpace_iff_empiricalError_zero

Topic: learning   Node: 97da31408da1

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.mem_versionSpace_iff_empiricalError_zero`. Lean proof by Dhruv Gupta, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/VersionSpace.lean (Copyright (c) 2026 Dhruv Gupta. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Version-space membership equals concept-class membership plus zero empirical error (measure-theoretic bridge).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal in
variable {α : Type*} {β : Type*} in
/-- Version-space membership equals concept-class membership plus zero empirical error (measure-theoretic bridge). -/
theorem Cslib.MachineLearning.PACLearning.mem_versionSpace_iff_empiricalError_zero
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    {m : ℕ} {C : ConceptClass α β} {S : LabeledSample α β m} {h : α → β} :
    h ∈ VersionSpace C S ↔ h ∈ C ∧ empiricalError h S = 0 := by
  refine and_congr_right fun _ => ?_
  unfold empiricalError empiricalMeasure error
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp
  · simp_all [Nat.pos_iff_ne_zero]
