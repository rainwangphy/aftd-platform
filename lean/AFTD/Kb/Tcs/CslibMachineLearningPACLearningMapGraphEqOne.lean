import AFTD.Prelude

/-!
# Cslib.MachineLearning.PACLearning.map_graph_eq_one

Topic: learning   Node: 3fbd34b49456

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.map_graph_eq_one`. Lean proof by Dhruv Gupta, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/VersionSpace.lean (Copyright (c) 2026 Dhruv Gupta. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Under the pushforward of a probability measure `P` along the graph map `x ↦ (x, c x)`, the graph of `c` has measure `1`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal in
variable {α : Type*} {β : Type*} in
/-- Under the pushforward of a probability measure `P` along the graph map `x ↦ (x, c x)`, the graph of `c` has measure `1`. -/
lemma Cslib.MachineLearning.PACLearning.map_graph_eq_one
    [MeasurableSpace α] [MeasurableSpace β]
    {c : α → β} (hcm : Measurable c) (P : Measure α) [IsProbabilityMeasure P]
    (hG : MeasurableSet {p : α × β | p.2 = c p.1}) :
    (P.map (fun x => (x, c x))) {p : α × β | p.2 = c p.1} = 1 := by
  have hφ : Measurable (fun x : α => (x, c x)) := by fun_prop
  rw [Measure.map_apply hφ hG]
  have hpre : (fun x : α => (x, c x)) ⁻¹' {p : α × β | p.2 = c p.1} = Set.univ := by
    ext x; simp
  rw [hpre, measure_univ]
