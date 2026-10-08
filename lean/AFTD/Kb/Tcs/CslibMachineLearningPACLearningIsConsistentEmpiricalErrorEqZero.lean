import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLearner
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningIsConsistent
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLabeledSample
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningEmpiricalError
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningVersionSpace
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningMemVersionSpaceIffEmpiricalErrorZero

/-!
# Cslib.MachineLearning.PACLearning.IsConsistent.empiricalError_eq_zero

Topic: learning   Node: 81e07a0fe447

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.IsConsistent.empiricalError_eq_zero`. Lean proof by Dhruv Gupta, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/VersionSpace.lean (Copyright (c) 2026 Dhruv Gupta. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A consistent learner has zero empirical error on every sample.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal in
variable {α : Type*} {β : Type*} in
/-- A consistent learner has zero empirical error on every sample. -/
theorem Cslib.MachineLearning.PACLearning.IsConsistent.empiricalError_eq_zero
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    {m : ℕ} {A : Learner α β m} {C : ConceptClass α β}
    (hA : IsConsistent A C) (S : LabeledSample α β m) :
    empiricalError (A S) S = 0 :=
  (mem_versionSpace_iff_empiricalError_zero.mp (hA S)).2
