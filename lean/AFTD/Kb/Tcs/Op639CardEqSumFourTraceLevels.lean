import AFTD.Prelude
import AFTD.Kb.Tcs.Op639CardEqSumFiberTraces

/-!
# op_639_card_eq_sum_four_trace_levels

Topic: combinatorics   Node: f1a2566ae182

Provenance: helper lemma. step towards op_639_intersecting_four_uniform_covering_four_card_le_forty_two

Let T be a 4-element transversal of F. Then the size of F is partitioned into the sum of the sizes of the trace fibers on T of cardinalities 4 (the full fiber), 3, 2, and 1.
-/

/-- For any transversal T of size 4 in F, the cardinality of F is the sum of the full fiber, triple fibers, doubleton fibers, and singleton fibers. -/
theorem op_639_card_eq_sum_four_trace_levels
    {V : Type*} [DecidableEq V] (F : Finset (Finset V)) (T : Finset V)
    (hT : T.card = 4) (hT_trans : ∀ e ∈ F, ¬Disjoint e T) :
    F.card = (F.filter (fun e => e ∩ T = T)).card +
      (∑ S ∈ T.powersetCard 3, (F.filter (fun e => e ∩ T = S)).card) +
      (∑ S ∈ T.powersetCard 2, (F.filter (fun e => e ∩ T = S)).card) +
      (∑ S ∈ T.powersetCard 1, (F.filter (fun e => e ∩ T = S)).card) := by
  open Finset in
  have h_fibers := op_639_card_eq_sum_fiber_traces F T hT_trans
  have h_erase : ∑ S ∈ T.powerset.erase ∅, (F.filter (fun e => e ∩ T = S)).card =
      ∑ S ∈ T.powerset, (F.filter (fun e => e ∩ T = S)).card := by
    apply Finset.sum_erase
    simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro e he h
    exact hT_trans e he (Finset.disjoint_iff_inter_eq_empty.mpr h)
  rw [h_erase] at h_fibers
  have h_split := Finset.sum_powerset (β := ℕ) T (fun S => (F.filter (fun e => e ∩ T = S)).card)
  rw [h_split, hT] at h_fibers
  have h_range : ∑ j ∈ range 5, (∑ S ∈ T.powersetCard j, (F.filter (fun e => e ∩ T = S)).card) =
      (∑ S ∈ T.powersetCard 0, (F.filter (fun e => e ∩ T = S)).card) +
      (∑ S ∈ T.powersetCard 1, (F.filter (fun e => e ∩ T = S)).card) +
      (∑ S ∈ T.powersetCard 2, (F.filter (fun e => e ∩ T = S)).card) +
      (∑ S ∈ T.powersetCard 3, (F.filter (fun e => e ∩ T = S)).card) +
      (∑ S ∈ T.powersetCard 4, (F.filter (fun e => e ∩ T = S)).card) := by
    repeat rw [Finset.sum_range_succ]
    rw [Finset.sum_range_zero, zero_add]
  rw [h_range] at h_fibers
  have h0 : (∑ S ∈ T.powersetCard 0, (F.filter (fun e => e ∩ T = S)).card) = 0 := by
    rw [Finset.powersetCard_zero, Finset.sum_singleton]
    simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro e he h
    exact hT_trans e he (Finset.disjoint_iff_inter_eq_empty.mpr h)
  have h4 : (∑ S ∈ T.powersetCard 4, (F.filter (fun e => e ∩ T = S)).card) =
      (F.filter (fun e => e ∩ T = T)).card := by
    have : T.powersetCard 4 = {T} := by rw [← hT, Finset.powersetCard_self]
    rw [this, Finset.sum_singleton]
  rw [h0, h4] at h_fibers
  omega
