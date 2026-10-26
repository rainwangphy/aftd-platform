import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsWellCovered
import AFTD.Kb.Tcs.SimpleGraphPower
import AFTD.Kb.Tcs.ForallPowerWellCoveredOfWellCoveredDiamLeTwo

/-!
# cycle_five_all_powers_well_covered

Topic: graphs   Node: 4b9c30c92906

Provenance: formalization of a published result. Source: arXiv:2610.09300 Example 3.7

For every positive integer d, the d-th power of the 5-cycle graph C_5 is well-covered.
-/

theorem cycle_five_all_powers_well_covered_dist_le_two_aux :
    ∀ u v : Fin 5, u = v ∨ (SimpleGraph.cycleGraph 5).Adj u v ∨
      ∃ w : Fin 5, (SimpleGraph.cycleGraph 5).Adj u w ∧ (SimpleGraph.cycleGraph 5).Adj w v := by
  decide

theorem cycle_five_all_powers_well_covered_edist_le_two (u v : Fin 5) :
    (SimpleGraph.cycleGraph 5).edist u v ≤ 2 := by
  rcases cycle_five_all_powers_well_covered_dist_le_two_aux u v with rfl | h | ⟨w, h1, h2⟩
  · rw [SimpleGraph.edist_self]; norm_num
  · exact (SimpleGraph.Walk.cons h SimpleGraph.Walk.nil).edist_le.trans (by simp)
  · exact (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 SimpleGraph.Walk.nil)).edist_le.trans (by simp)

theorem cycle_five_all_powers_well_covered_diam_le_two :
    (SimpleGraph.cycleGraph 5).diam ≤ 2 := by
  have hediam : (SimpleGraph.cycleGraph 5).ediam ≤ 2 := by
    rw [SimpleGraph.ediam_le_iff]
    exact cycle_five_all_powers_well_covered_edist_le_two
  rw [SimpleGraph.diam]
  exact ENat.toNat_le_of_le_natCast hediam

theorem cycle_five_all_powers_well_covered_indep_card_le_two (s : Finset (Fin 5))
    (hs : (SimpleGraph.cycleGraph 5).IsIndepSet (s : Set (Fin 5))) :
    s.card ≤ 2 := by
  revert s hs
  decide

theorem cycle_five_all_powers_well_covered_indep_extend (s : Finset (Fin 5))
    (hs : (SimpleGraph.cycleGraph 5).IsIndepSet (s : Set (Fin 5))) (hcard : s.card < 2) :
    ∃ v : Fin 5, v ∉ s ∧ (SimpleGraph.cycleGraph 5).IsIndepSet ((insert v s : Finset (Fin 5)) : Set (Fin 5)) := by
  revert s hs hcard
  decide

theorem cycle_five_all_powers_well_covered_maximal_card (s : Finset (Fin 5))
    (hs : Maximal (fun u : Finset (Fin 5) => (SimpleGraph.cycleGraph 5).IsIndepSet (u : Set (Fin 5))) s) :
    s.card = 2 := by
  have hle : s.card ≤ 2 := cycle_five_all_powers_well_covered_indep_card_le_two s hs.1
  have hge : 2 ≤ s.card := by
    by_contra! hlt
    obtain ⟨v, hv_notin, hv_indep⟩ := cycle_five_all_powers_well_covered_indep_extend s hs.1 hlt
    have hsub : s ≤ insert v s := Finset.subset_insert v s
    have heq : insert v s ≤ s := hs.2 hv_indep hsub
    exact hv_notin (heq (Finset.mem_insert_self v s))
  omega

theorem cycle_five_all_powers_well_covered_is_well_covered :
    simple_graph_is_well_covered (SimpleGraph.cycleGraph 5) := by
  intro s t hs ht
  rw [cycle_five_all_powers_well_covered_maximal_card s hs,
      cycle_five_all_powers_well_covered_maximal_card t ht]

/-- Every power of the 5-cycle graph C_5 is well-covered. -/
theorem cycle_five_all_powers_well_covered :
    ∀ d : ℕ, 1 ≤ d → simple_graph_is_well_covered (simple_graph_power (SimpleGraph.cycleGraph 5) d) := by
  have hconn : (SimpleGraph.cycleGraph 5).Connected := @SimpleGraph.cycleGraph_connected 4
  exact forall_power_well_covered_of_well_covered_diam_le_two
    (SimpleGraph.cycleGraph 5) hconn
    cycle_five_all_powers_well_covered_diam_le_two
    cycle_five_all_powers_well_covered_is_well_covered
