import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLabeledSample
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningVersionSpace
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningPiMapGraphEqOne

/-!
# Cslib.MachineLearning.PACLearning.ae_mem_versionSpace_of_realizable

Topic: learning   Node: 36b5704bd1bc

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.ae_mem_versionSpace_of_realizable`. Lean proof by Dhruv Gupta, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/VersionSpace.lean (Copyright (c) 2026 Dhruv Gupta. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Under iid sampling from the realizable joint distribution induced by `c ∈ C` and a probability measure `P` on `α`, the target concept `c` lies in the version space almost surely.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal in
variable {α : Type*} {β : Type*} in
/-- Under iid sampling from the realizable joint distribution induced by `c ∈ C` and a probability measure `P` on `α`, the target concept `c` lies in the version space almost surely. -/
theorem Cslib.MachineLearning.PACLearning.ae_mem_versionSpace_of_realizable
    [MeasurableSpace α] [MeasurableSpace β]
    {C : ConceptClass α β} {c : α → β} (hc : c ∈ C) (hcm : Measurable c)
    (hG : MeasurableSet {p : α × β | p.2 = c p.1})
    (P : Measure α) [IsProbabilityMeasure P] (m : ℕ) :
    ∀ᵐ S : LabeledSample α β m
      ∂(Measure.pi (fun _ : Fin m => P.map (fun x => (x, c x)))),
      c ∈ VersionSpace C S := by
  have hφ : Measurable (fun x : α => (x, c x)) := by fun_prop
  have : IsProbabilityMeasure (P.map (fun x : α => (x, c x))) :=
    Measure.isProbabilityMeasure_map hφ.aemeasurable
  rw [ae_iff]
  have hsub : {S : Fin m → α × β | ¬ c ∈ VersionSpace C S} ⊆
      (Set.univ.pi (fun _ : Fin m => {p : α × β | p.2 = c p.1}))ᶜ := by
    intro S hS hcontra
    exact hS ⟨hc, by simp_all⟩
  have hcompl : (Measure.pi (fun _ : Fin m => P.map (fun x : α => (x, c x))))
      ((Set.univ.pi (fun _ : Fin m => {p : α × β | p.2 = c p.1}))ᶜ) = 0 := by
    rw [prob_compl_eq_one_sub (MeasurableSet.univ_pi fun _ => hG),
        pi_map_graph_eq_one hcm P hG, tsub_self]
  exact measure_mono_null hsub hcompl
