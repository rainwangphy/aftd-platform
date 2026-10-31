import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsWellCovered
import AFTD.Kb.Tcs.SimpleGraphPower

/-!
# cycle_seven_power_ge_three_well_covered

Topic: graphs   Node: 6cd77725ada5

Provenance: helper lemma. step towards cycle_seven_all_powers_well_covered

Every power d ≥ 3 of the 7-cycle graph is well-covered: since diam(C_7) = 3 ≤ d, the d-th power is the complete graph K_7 and every maximal independent set has size 1.
-/

/-- Every power d ≥ 3 of the 7-cycle graph is well-covered: since diam(C_7) = 3 ≤ d, the d-th power is the complete graph K_7 and every maximal independent set has size 1. -/
theorem cycle_seven_power_ge_three_well_covered (d : ℕ) (hd : 3 ≤ d) :
    simple_graph_is_well_covered (simple_graph_power (SimpleGraph.cycleGraph 7) d) := by
  have hsub_succ : ∀ u : Fin 7, (u + 1) - u = 1 := by decide
  have hadd2 : ∀ u : Fin 7, (u + 1) + 1 = u + 2 := by decide
  have hadd3 : ∀ u : Fin 7, (u + 2) + 1 = u + 3 := by decide
  have hpred1 : ∀ u : Fin 7, (u - 1) + 1 = u := by decide
  have hpred2 : ∀ u : Fin 7, (u - 2) + 2 = u := by decide
  have hpred3 : ∀ u : Fin 7, (u - 3) + 3 = u := by decide
  have hdiff : ∀ u v : Fin 7, u ≠ v →
      (v = u + 1 ∨ v = u + 2 ∨ v = u + 3 ∨ v = u - 1 ∨ v = u - 2 ∨ v = u - 3) := by decide
  have hadj_succ : ∀ u : Fin 7, (SimpleGraph.cycleGraph 7).Adj u (u + 1) := by
    intro u
    rw [SimpleGraph.cycleGraph_adj]
    exact Or.inr (hsub_succ u)
  have hed1 : ∀ u : Fin 7, (SimpleGraph.cycleGraph 7).edist u (u + 1) = 1 := fun u =>
    SimpleGraph.edist_eq_one_iff_adj.mpr (hadj_succ u)
  have hed2 : ∀ u : Fin 7, (SimpleGraph.cycleGraph 7).edist u (u + 2) ≤ 2 := by
    intro u
    have htri := SimpleGraph.edist_triangle (G := SimpleGraph.cycleGraph 7)
      (u := u) (v := u + 1) (w := (u + 1) + 1)
    have ht : (SimpleGraph.cycleGraph 7).edist u ((u + 1) + 1) ≤ 2 := by
      calc (SimpleGraph.cycleGraph 7).edist u ((u + 1) + 1)
          ≤ (SimpleGraph.cycleGraph 7).edist u (u + 1) +
              (SimpleGraph.cycleGraph 7).edist (u + 1) ((u + 1) + 1) := htri
        _ = 1 + 1 := by rw [hed1 u, hed1 (u + 1)]
        _ = 2 := by norm_num
    rw [← hadd2 u]
    exact ht
  have hed3 : ∀ u : Fin 7, (SimpleGraph.cycleGraph 7).edist u (u + 3) ≤ 3 := by
    intro u
    have htri := SimpleGraph.edist_triangle (G := SimpleGraph.cycleGraph 7)
      (u := u) (v := u + 2) (w := (u + 2) + 1)
    have ht : (SimpleGraph.cycleGraph 7).edist u ((u + 2) + 1) ≤ 3 := by
      calc (SimpleGraph.cycleGraph 7).edist u ((u + 2) + 1)
          ≤ (SimpleGraph.cycleGraph 7).edist u (u + 2) +
              (SimpleGraph.cycleGraph 7).edist (u + 2) ((u + 2) + 1) := htri
        _ ≤ 2 + 1 := by
            apply add_le_add
            · exact hed2 u
            · rw [hed1 (u + 2)]
        _ = 3 := by norm_num
    rw [← hadd3 u]
    exact ht
  have hdist3 : ∀ u v : Fin 7, u ≠ v → (SimpleGraph.cycleGraph 7).edist u v ≤ 3 := by
    intro u v hv
    rcases hdiff u v hv with h | h | h | h | h | h
    · rw [h, hed1 u]; norm_num
    · rw [h]; exact le_trans (hed2 u) (by norm_num)
    · rw [h]; exact hed3 u
    · rw [h, SimpleGraph.edist_comm]
      have h' := hed1 (u - 1)
      rw [hpred1 u] at h'
      rw [h']; norm_num
    · rw [h, SimpleGraph.edist_comm]
      have h' := hed2 (u - 2)
      rw [hpred2 u] at h'
      exact le_trans h' (by norm_num)
    · rw [h, SimpleGraph.edist_comm]
      have h' := hed3 (u - 3)
      rw [hpred3 u] at h'
      exact h'
  have hadj_complete : ∀ u v : Fin 7, u ≠ v →
      (simple_graph_power (SimpleGraph.cycleGraph 7) d).Adj u v := by
    intro u v hv
    exact ⟨hv, le_trans (hdist3 u v hv) (by exact_mod_cast hd)⟩
  have hcard : ∀ s : Finset (Fin 7),
      Maximal (fun u : Finset (Fin 7) =>
        (simple_graph_power (SimpleGraph.cycleGraph 7) d).IsIndepSet (↑u)) s → s.card = 1 := by
    intro s hs
    obtain ⟨hind, hmax⟩ := hs
    have hle : s.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      by_contra hne
      exact hind ha hb hne (hadj_complete a b hne)
    have hne : s.Nonempty := by
      rcases Finset.eq_empty_or_nonempty s with h | h
      · exfalso
        have hsub : s ⊆ ({0} : Finset (Fin 7)) := by rw [h]; exact Finset.empty_subset _
        have hind0 : (simple_graph_power (SimpleGraph.cycleGraph 7) d).IsIndepSet
            (↑({0} : Finset (Fin 7)) : Set (Fin 7)) := by
          rw [SimpleGraph.isIndepSet_iff]
          intro a ha b hb hne'
          rw [Finset.coe_singleton, Set.mem_singleton_iff] at ha hb
          exact absurd (ha.trans hb.symm) hne'
        have hle' := hmax hind0 hsub
        have hmem : (0 : Fin 7) ∈ s := hle' (by simp)
        rw [h] at hmem
        simp at hmem
      · exact h
    exact le_antisymm hle (Finset.card_pos.mpr hne)
  intro s t hs ht
  rw [hcard s hs, hcard t ht]
