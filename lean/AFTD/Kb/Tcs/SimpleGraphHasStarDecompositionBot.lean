import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphHasStarDecomposition

/-!
# simple_graph_has_star_decomposition_bot

Topic: graphs   Node: cdc1b8258357

Provenance: helper lemma. folklore

For any natural number q, the empty graph on one vertex has a star decomposition into copies of K_{1,q}.
-/

/-- Sanity lemma: the empty graph on one vertex vacuously has a star decomposition into copies of K_{1,q}. -/
theorem simple_graph_has_star_decomposition_bot (q : ℕ) :
    simple_graph_has_star_decomposition (⊥ : SimpleGraph (Fin 1)) q := by
  exact ⟨∅, by simp [Set.PairwiseDisjoint]⟩
