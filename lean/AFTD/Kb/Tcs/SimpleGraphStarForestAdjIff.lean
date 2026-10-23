import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphStarForest

/-!
# simple_graph_star_forest_adj_iff

Topic: graphs   Node: 846993c2715d

Provenance: helper lemma. helper for arXiv:2610.25958 (Size Ramsey numbers of star forests with two components on one side), Lemma 2.3 (PR-280)

Adjacency in the star forest: same component, one vertex the centre and the other a leaf.
-/

theorem simple_graph_star_forest_adj_iff (q : ℕ) (n : Fin q → ℕ) (u v : Σ i : Fin q, Option (Fin (n i))) :
    (simple_graph_star_forest q n).Adj u v ↔
      u.1 = v.1 ∧ ((u.2 = none ∧ v.2 ≠ none) ∨ (u.2 ≠ none ∧ v.2 = none)) :=
  Iff.rfl
