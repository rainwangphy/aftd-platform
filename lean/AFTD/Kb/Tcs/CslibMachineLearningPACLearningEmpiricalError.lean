import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLabeledSample
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningError
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningEmpiricalMeasure

/-!
# Cslib.MachineLearning.PACLearning.empiricalError

Topic: learning   Node: 565226ac1e64

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.empiricalError`. Lean proof by Dhruv Gupta, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/VersionSpace.lean (Copyright (c) 2026 Dhruv Gupta. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The *empirical 0-1 error* of `h` on `S`: the empirical distribution's mass on the disagreement set.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal in
variable {α : Type*} {β : Type*} in
variable [MeasurableSpace α] [MeasurableSpace β] in
/-- The *empirical 0-1 error* of `h` on `S`: the empirical distribution's mass on the disagreement set. -/
noncomputable def Cslib.MachineLearning.PACLearning.empiricalError {m : ℕ} (h : α → β) (S : LabeledSample α β m) :
    ℝ≥0∞ :=
  error (empiricalMeasure S) h
