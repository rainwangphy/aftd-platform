import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLabeledSample

/-!
# Cslib.MachineLearning.PACLearning.empiricalMeasure

Topic: learning   Node: 78082b6260c6

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.empiricalMeasure`. Lean proof by Dhruv Gupta, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/VersionSpace.lean (Copyright (c) 2026 Dhruv Gupta. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The *empirical distribution* of a labeled sample: the uniform mixture of Dirac measures at each sample point. Equals the zero measure when `m = 0`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal in
variable {α : Type*} {β : Type*} in
variable [MeasurableSpace α] [MeasurableSpace β] in
/-- The *empirical distribution* of a labeled sample: the uniform mixture of Dirac measures at each sample point. Equals the zero measure when `m = 0`. -/
noncomputable def Cslib.MachineLearning.PACLearning.empiricalMeasure {m : ℕ} (S : LabeledSample α β m) :
    Measure (α × β) :=
  if _hm : m = 0 then 0
  else (m : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (S i)
