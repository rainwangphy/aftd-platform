import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningMapGraphEqOne

/-!
# Cslib.MachineLearning.PACLearning.pi_map_graph_eq_one

Topic: learning   Node: 45c50f72b708

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.pi_map_graph_eq_one`. Lean proof by Dhruv Gupta, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/VersionSpace.lean (Copyright (c) 2026 Dhruv Gupta. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The iid product of the realizable joint distribution assigns measure `1` to the set of samples where every coordinate lies on the graph of `c`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal in
variable {α : Type*} {β : Type*} in
/-- The iid product of the realizable joint distribution assigns measure `1` to the set of samples where every coordinate lies on the graph of `c`. -/
lemma Cslib.MachineLearning.PACLearning.pi_map_graph_eq_one
    [MeasurableSpace α] [MeasurableSpace β]
    {c : α → β} (hcm : Measurable c) (P : Measure α) [IsProbabilityMeasure P]
    (hG : MeasurableSet {p : α × β | p.2 = c p.1}) {m : ℕ} :
    (Measure.pi (fun _ : Fin m => P.map (fun x => (x, c x))))
      (Set.univ.pi (fun _ : Fin m => {p : α × β | p.2 = c p.1})) = 1 := by
  have hφ : Measurable (fun x : α => (x, c x)) := by fun_prop
  have : IsProbabilityMeasure (P.map (fun x : α => (x, c x))) :=
    Measure.isProbabilityMeasure_map hφ.aemeasurable
  rw [Measure.pi_pi]
  simp [map_graph_eq_one hcm P hG]
