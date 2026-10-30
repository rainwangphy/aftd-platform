import AFTD.Prelude

/-!
# op_639_card_eq_sum_fiber_traces

Topic: combinatorics   Node: f8d48243947a

Provenance: helper lemma. step towards op_639_intersecting_four_uniform_covering_four_card_le_forty_two

For any transversal T of F, every edge e in F has non-empty trace e ∩ T on T, so F is partitioned into the fibers of the map e ↦ e ∩ T over non-empty subsets of T.
-/

/-- The size of F equals the sum of sizes of trace fibers e ∩ T over non-empty subsets S of T. -/
theorem op_639_card_eq_sum_fiber_traces
    {V : Type*} [DecidableEq V] (F : Finset (Finset V)) (T : Finset V)
    (hT_trans : ∀ e ∈ F, ¬Disjoint e T) :
    F.card = ∑ S ∈ T.powerset.erase ∅, (F.filter (fun e => e ∩ T = S)).card := by
  refine Finset.card_eq_sum_card_fiberwise (f := fun e : Finset V => e ∩ T) (s := F)
    (t := T.powerset.erase ∅) ?_
  intro e he
  change e ∩ T ∈ T.powerset.erase ∅
  rw [Finset.mem_erase, Finset.mem_powerset]
  exact ⟨fun h => hT_trans e he ((Finset.disjoint_iff_inter_eq_empty).mpr h),
    Finset.inter_subset_right⟩
