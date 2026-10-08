import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLearner
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLabeledSample
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningError
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningOptimalError

/-!
# Cslib.MachineLearning.PACLearning.IsPACLearnerFor

Topic: learning   Node: 1070c1c855dc

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.IsPACLearnerFor`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/Defs.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`IsPACLearnerFor m ε δ C 𝒟` asserts that there exists a learner using `m` samples that is `(ε, δ)`-correct for the concept class `C` over the distribution family `𝒟`: for every probability measure `D ∈ 𝒟` on `α × β`, the probability (over i.i.d. samples from `D`) that the learner's hypothesis has error exceeding `opt_C(D) + ε` is at most `δ`. The parameters `ε` and `δ` are elements of `Set.Ioo (0 : ℝ≥0) 1`, bundling the value with the proof that it lies in `(0, 1)`. This ensures the condition is non-vacuous: `ε < 1` prevents the error threshold from exceeding the maximum possible error under a probability measure, and `δ < 1` prevents the confidence bound from being trivially satisfied.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal NNReal in
variable {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β] in
/-- `IsPACLearnerFor m ε δ C 𝒟` asserts that there exists a learner using `m` samples that is `(ε, δ)`-correct for the concept class `C` over the distribution family `𝒟`: for every probability measure `D ∈ 𝒟` on `α × β`, the probability (over i.i.d. samples from `D`) that the learner's hypothesis has error exceeding `opt_C(D) + ε` is at most `δ`. The parameters `ε` and `δ` are elements of `Set.Ioo (0 : ℝ≥0) 1`, bundling the value with the proof that it lies in `(0, 1)`. This ensures the condition is non-vacuous: `ε < 1` prevents the error threshold from exceeding the maximum possible error under a probability measure, and `δ < 1` prevents the confidence bound from being trivially satisfied. -/
noncomputable def Cslib.MachineLearning.PACLearning.IsPACLearnerFor (m : ℕ) (ε δ : Set.Ioo (0 : ℝ≥0) 1)
    (C : ConceptClass α β) (𝒟 : Set (Measure (α × β))) : Prop :=
  ∃ A : Learner α β m,
    ∀ (D : Measure (α × β)) [IsProbabilityMeasure D], D ∈ 𝒟 →
      (Measure.pi (fun _ : Fin m => D))
        {S : LabeledSample α β m |
          error D (A S) > optimalError D C + ↑ε.val} ≤ ↑δ.val
