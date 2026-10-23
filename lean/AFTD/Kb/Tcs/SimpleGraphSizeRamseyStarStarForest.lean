import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphSizeRamseyStarStarForestArrows
import AFTD.Kb.Tcs.SimpleGraphSizeRamseyStarStarForestEdgesGe
import AFTD.Kb.Tcs.SimpleGraphSizeRamseyLeOfArrows
import AFTD.Kb.Tcs.SimpleGraphSizeRamsey
import AFTD.Kb.Tcs.SimpleGraphStarForest
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.SimpleGraphSizeRamseyArrows
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# simple_graph_size_ramsey_star_star_forest

Topic: graphs   Node: 6b8ae08225c7

Provenance: formalization of a published result. Source: arXiv:2610.25958 (Size Ramsey numbers of star forests with two components on one side), Lemma 2.3

Lemma 2.3 of arXiv:2610.25958: for positive integers p, q, n_1 ≥ ... ≥ n_q, r̂(K_{1,p}, ⊔_{i=1}^q K_{1,n_i}) = ∑_{i=1}^q (p + n_i - 1).
-/

theorem simple_graph_size_ramsey_star_star_forest (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (n : Fin q → ℕ) (hn : ∀ i, 0 < n i) (hmono : Antitone n) :
    simple_graph_size_ramsey (completeBipartiteGraph (Fin 1) (Fin p))
      (simple_graph_star_forest q n) = ∑ i, (p + n i - 1) := by
  apply le_antisymm
  · obtain ⟨k, G, hcard, hG⟩ := simple_graph_size_ramsey_star_star_forest_arrows p q hp n hn
    exact hcard ▸ simple_graph_size_ramsey_le_of_arrows _ _ k G hG
  · apply le_csInf
    · obtain ⟨k, G, hcard, hG⟩ := simple_graph_size_ramsey_star_star_forest_arrows p q hp n hn
      exact ⟨_, k, G, hcard, hG⟩
    · rintro m ⟨k, G, rfl, hG⟩
      exact simple_graph_size_ramsey_star_star_forest_edges_ge p q hp n hn k G hG
