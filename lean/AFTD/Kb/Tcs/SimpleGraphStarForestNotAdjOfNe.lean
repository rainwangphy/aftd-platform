import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphStarForest

/-!
# simple_graph_star_forest_not_adj_of_ne

Topic: graphs   Node: 5239d5fce861

Provenance: helper lemma. sanity lemma for simple_graph_star_forest

Sanity: vertices in different components of the star forest are not adjacent.
-/

theorem simple_graph_star_forest_not_adj_of_ne (q : ℕ) (n : Fin q → ℕ) (u v : Σ i : Fin q, Option (Fin (n i)))
    (h : u.1 ≠ v.1) : ¬ (simple_graph_star_forest q n).Adj u v := fun hadj => h hadj.1
