import AFTD.Prelude
import AFTD.Kb.Tcs.CompleteGraphTwoAllPowersWellCovered
import AFTD.Kb.Tcs.DiamBoxProdCompleteGraph
import AFTD.Kb.Tcs.BoxProdCompleteGraphAllPowersWellCovered
import AFTD.Kb.Tcs.SimpleGraphPower
import AFTD.Kb.Tcs.SimpleGraphIsWellCovered
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# exists_connected_all_powers_well_covered_diam_ge

Topic: graphs   Node: 6cf7fec39a4b

Provenance: formalization of a published result. Source: arXiv:2611.03956 Corollary 2.13

For every positive integer D, there exists a finite connected simple graph G with diameter at least D such that every positive power G^d (d ≥ 1) is well-covered.
-/

/-- Existence of connected graphs with well-covered powers of arbitrarily large diameter. -/
theorem exists_connected_all_powers_well_covered_diam_ge (D : ℕ) (hD : 0 < D) :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      G.Connected ∧
      D ≤ G.diam ∧
      ∀ d : ℕ, 1 ≤ d → simple_graph_is_well_covered (simple_graph_power G d) := by
  have strong : ∀ n : ℕ, 1 ≤ n → ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      2 ≤ Fintype.card V ∧ G.Connected ∧ n ≤ G.diam ∧
      ∀ d : ℕ, 1 ≤ d → simple_graph_is_well_covered (simple_graph_power G d) := by
    intro n hn
    induction n with
    | zero => omega
    | succ n ih =>
      cases n with
      | zero =>
        refine ⟨Fin 2, inferInstance, SimpleGraph.completeGraph (Fin 2), ?_, ?_, ?_, ?_⟩
        · simp
        · exact complete_graph_two_all_powers_well_covered.1
        · rw [complete_graph_two_all_powers_well_covered.2.1]
        · exact complete_graph_two_all_powers_well_covered.2.2
      | succ k =>
        have hk : 1 ≤ Nat.succ k := by omega
        obtain ⟨V, instV, G, hcard, hconn, hdiam, hwc⟩ := ih hk
        letI := instV
        haveI : Nonempty V := hconn.nonempty
        let t := Fintype.card V + 2
        have ht_gt : Fintype.card V < t := by dsimp [t]; omega
        have ht2 : 2 ≤ t := by dsimp [t]; omega
        haveI : Nonempty (Fin t) := by
          rw [← Fintype.card_pos_iff]
          simp [t]
        have hcomp : (SimpleGraph.completeGraph (Fin t)).Connected := by
          rw [SimpleGraph.completeGraph_eq_top]
          exact SimpleGraph.connected_top
        refine ⟨V × Fin t, inferInstance, G □ SimpleGraph.completeGraph (Fin t), ?_, ?_, ?_, ?_⟩
        · rw [Fintype.card_prod, Fintype.card_fin]
          have : 1 ≤ Fintype.card V := by omega
          nlinarith
        · exact SimpleGraph.Connected.boxProd hconn hcomp
        · rw [diam_boxProd_completeGraph G hconn t ht2]
          omega
        · intro d hd
          exact boxProd_completeGraph_all_powers_well_covered G hconn hcard hwc t ht_gt d hd
  obtain ⟨V, instV, G, hcard, hconn, hdiam, hwc⟩ := strong D hD
  exact ⟨V, instV, G, hconn, hdiam, hwc⟩
