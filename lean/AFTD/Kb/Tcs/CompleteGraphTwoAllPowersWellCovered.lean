import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphPower
import AFTD.Kb.Tcs.ForallPowerWellCoveredOfWellCoveredDiamLeTwo
import AFTD.Kb.Tcs.SimpleGraphIsWellCovered

/-!
# complete_graph_two_all_powers_well_covered

Topic: graphs   Node: ce3f4ef56fd5

Provenance: helper lemma. arXiv:2611.03956 Lemma 2.8 and Corollary 2.13

The complete graph on 2 vertices K_2 is connected, has diameter 1, and every positive power K_2^d (d ≥ 1) is well-covered.
-/

/-- The complete graph K_2 is connected, has diameter 1, and has well-covered powers. -/
theorem complete_graph_two_all_powers_well_covered :
    (SimpleGraph.completeGraph (Fin 2)).Connected ∧
    (SimpleGraph.completeGraph (Fin 2)).diam = 1 ∧
    ∀ d : ℕ, 1 ≤ d → simple_graph_is_well_covered (simple_graph_power (SimpleGraph.completeGraph (Fin 2)) d) := by
  have hconn : (SimpleGraph.completeGraph (Fin 2)).Connected := SimpleGraph.connected_top
  have hdiam : (SimpleGraph.completeGraph (Fin 2)).diam = 1 := by
    change (⊤ : SimpleGraph (Fin 2)).diam = 1
    exact SimpleGraph.diam_top
  refine ⟨hconn, hdiam, ?_⟩
  apply forall_power_well_covered_of_well_covered_diam_le_two
  · exact hconn
  · rw [hdiam]
    omega
  · change simple_graph_is_well_covered (⊤ : SimpleGraph (Fin 2))
    intro s t hs ht
    have hcard : ∀ u : Finset (Fin 2), Maximal (fun (w : Finset (Fin 2)) => (⊤ : SimpleGraph (Fin 2)).IsIndepSet (w : Set (Fin 2))) u → u.card = 1 := by
      intro u hu
      obtain ⟨v0⟩ : Nonempty (Fin 2) := inferInstance
      by_cases hne : u.Nonempty
      · obtain ⟨a, ha⟩ := hne
        rw [Finset.card_eq_one]
        refine ⟨a, Finset.eq_singleton_iff_unique_mem.2 ⟨ha, fun b hb => ?_⟩⟩
        by_contra hba
        have : (⊤ : SimpleGraph (Fin 2)).Adj b a := hba
        exact hu.1 hb ha hba this
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        subst hne
        have hv : (⊤ : SimpleGraph (Fin 2)).IsIndepSet (({v0} : Finset (Fin 2)) : Set (Fin 2)) := by simp
        have := hu.2 hv (Finset.empty_subset _)
        simp at this
    rw [hcard s hs, hcard t ht]
