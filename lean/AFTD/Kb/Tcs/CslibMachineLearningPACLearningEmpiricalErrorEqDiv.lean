import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLabeledSample
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningEmpiricalError
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningEmpiricalMiscount
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningError
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningEmpiricalMeasure

/-!
# Cslib.MachineLearning.PACLearning.empiricalError_eq_div

Topic: learning   Node: 56eaf992bace

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.empiricalError_eq_div`. Lean proof by Dhruv Gupta, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/VersionSpace.lean (Copyright (c) 2026 Dhruv Gupta. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The empirical 0-1 error equals the empirical miscount divided by the sample size.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal in
variable {α : Type*} {β : Type*} in
/-- The empirical 0-1 error equals the empirical miscount divided by the sample size. -/
theorem Cslib.MachineLearning.PACLearning.empiricalError_eq_div [DecidableEq β]
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    {m : ℕ} (hm : 0 < m) (h : α → β) (S : LabeledSample α β m) :
    empiricalError h S = (empiricalMiscount h S : ℝ≥0∞) / m := by
  have hm_ne : m ≠ 0 := hm.ne'
  unfold empiricalError empiricalMeasure error empiricalMiscount
  rw [dif_neg hm_ne, Measure.smul_apply, Measure.finsetSum_apply]
  simp only [Measure.dirac_apply, Set.indicator, Set.mem_ofPred_eq, Pi.one_apply, smul_eq_mul]
  rw [Finset.sum_boole, ← ENNReal.div_eq_inv_mul]
