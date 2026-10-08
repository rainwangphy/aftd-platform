import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningError
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningHypothesisError

/-!
# Cslib.MachineLearning.PACLearning.error_map_eq_hypothesisError

Topic: learning   Node: aebd1117bf46

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.error_map_eq_hypothesisError`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/Defs.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Under a realizable distribution `P.map (x ↦ (x, c(x)))`, the general 0-1 `error` coincides with the binary `hypothesisError P h c`, where `h` and `c` are viewed as subsets of `α` via the characteristic function `decide (· ∈ ·)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal NNReal in
variable {α : Type*} [MeasurableSpace α] in
open Classical in
/-- Under a realizable distribution `P.map (x ↦ (x, c(x)))`, the general 0-1 `error` coincides with the binary `hypothesisError P h c`, where `h` and `c` are viewed as subsets of `α` via the characteristic function `decide (· ∈ ·)`. -/
theorem Cslib.MachineLearning.PACLearning.error_map_eq_hypothesisError (P : Measure α) (h c : Set α)
    (hh : MeasurableSet h) (hc : MeasurableSet c) :
    error (P.map (fun x => (x, decide (x ∈ c)))) (fun x => decide (x ∈ h)) =
    hypothesisError P h c := by
  simp only [error, hypothesisError]
  have hf : Measurable (fun x => (x, decide (x ∈ c))) :=
    Measurable.prodMk measurable_id
      (measurable_to_bool (by convert hc using 1; ext x; simp [decide_eq_true_eq]))
  rw [Measure.map_apply_of_aemeasurable hf.aemeasurable]
  · congr 1; ext x
    by_cases hx : x ∈ h <;> simp_all [symmDiff_def]
  · convert (hh.prod (measurableSet_singleton false)).union
      (hh.compl.prod (measurableSet_singleton true)) using 1
    ext ⟨x, b⟩; cases b <;> simp
