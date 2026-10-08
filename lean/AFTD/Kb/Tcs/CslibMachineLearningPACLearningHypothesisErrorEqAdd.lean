import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningHypothesisError
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningFalsePositiveError
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningFalseNegativeError

/-!
# Cslib.MachineLearning.PACLearning.hypothesisError_eq_add

Topic: learning   Node: 8764bd1825a0

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.hypothesisError_eq_add`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/Defs.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The total hypothesis error decomposes as the sum of false positive and false negative errors, since `h ∆ c = (h \ c) ∪ (c \ h)` is a disjoint union.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal NNReal in
variable {α : Type*} [MeasurableSpace α] in
/-- The total hypothesis error decomposes as the sum of false positive and false negative errors, since `h ∆ c = (h \ c) ∪ (c \ h)` is a disjoint union. -/
theorem Cslib.MachineLearning.PACLearning.hypothesisError_eq_add {P : Measure α} {h c : Set α}
    (hh : MeasurableSet h) (hc : MeasurableSet c) :
    hypothesisError P h c = falsePositiveError P h c + falseNegativeError P h c := by
  simp only [hypothesisError, falsePositiveError, falseNegativeError, symmDiff_def, sup_eq_union]
  exact measure_union disjoint_sdiff_sdiff (hc.diff hh)
