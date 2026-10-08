import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningIsPACLearnerFor
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningIsRPACLearnerFor
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLearner
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLabeledSample
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningError
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningOptimalError

/-!
# Cslib.MachineLearning.PACLearning.IsPACLearnerFor.toIsRPACLearnerFor

Topic: learning   Node: a9e1e6ddc698

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.IsPACLearnerFor.toIsRPACLearnerFor`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/Defs.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Every deterministic PAC learner is in particular a randomized PAC learner (with the trivial one-point randomness space `PUnit`).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal NNReal in
variable {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β] in
/-- Every deterministic PAC learner is in particular a randomized PAC learner (with the trivial one-point randomness space `PUnit`). -/
theorem Cslib.MachineLearning.PACLearning.IsPACLearnerFor.toIsRPACLearnerFor {m : ℕ} {ε δ : Set.Ioo (0 : ℝ≥0) 1}
    {C : ConceptClass α β} {𝒟 : Set (Measure (α × β))}
    (h : IsPACLearnerFor m ε δ C 𝒟) :
    IsRPACLearnerFor m ε δ C 𝒟 := by
  obtain ⟨A, hA⟩ := h
  refine ⟨PUnit, inferInstance, Measure.dirac PUnit.unit, inferInstance, fun _ => A, ?_⟩
  intro D _ hD
  refine ⟨measurable_const.aemeasurable, ?_⟩
  simp only [gt_iff_lt, lintegral_const, measure_univ, mul_one]
  exact hA D hD
