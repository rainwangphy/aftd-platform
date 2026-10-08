import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLearner
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningIsConsistent
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLabeledSample
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningEmpiricalMiscount
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningVersionSpace
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningMemVersionSpaceIffEmpiricalMiscountZero

/-!
# Cslib.MachineLearning.PACLearning.IsConsistent.empiricalMiscount_eq_zero

Topic: learning   Node: fd794078c82b

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.IsConsistent.empiricalMiscount_eq_zero`. Lean proof by Dhruv Gupta, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/VersionSpace.lean (Copyright (c) 2026 Dhruv Gupta. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A consistent learner has zero empirical miscount on every sample.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal in
variable {α : Type*} {β : Type*} in
/-- A consistent learner has zero empirical miscount on every sample. -/
theorem Cslib.MachineLearning.PACLearning.IsConsistent.empiricalMiscount_eq_zero [DecidableEq β]
    {m : ℕ} {A : Learner α β m} {C : ConceptClass α β} (hA : IsConsistent A C)
    (S : LabeledSample α β m) :
    empiricalMiscount (A S) S = 0 :=
  (mem_versionSpace_iff_empiricalMiscount_zero.mp (hA S)).2
