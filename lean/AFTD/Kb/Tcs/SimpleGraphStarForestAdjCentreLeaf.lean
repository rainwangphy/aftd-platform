import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphStarForest

/-!
# simple_graph_star_forest_adj_centre_leaf

Topic: graphs   Node: 74ff786fdd28

Provenance: helper lemma. sanity lemma for simple_graph_star_forest

Sanity: in the star forest, the centre of component i is adjacent to each of its leaves.
-/

theorem simple_graph_star_forest_adj_centre_leaf (q : ℕ) (n : Fin q → ℕ) (i : Fin q) (j : Fin (n i)) :
    (simple_graph_star_forest q n).Adj ⟨i, none⟩ ⟨i, some j⟩ :=
  ⟨rfl, Or.inl ⟨rfl, by simp⟩⟩
