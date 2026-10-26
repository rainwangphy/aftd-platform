import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsDominating

/-!
# simple_graph_is_dominating_univ

Topic: graphs   Node: 83f4c07bded3

Provenance: helper lemma. folklore

In any simple graph G, the entire vertex set is a dominating set.
-/

/-- The universal set of vertices is a dominating set. -/
theorem simple_graph_is_dominating_univ {V : Type*} (G : SimpleGraph V) :
    simple_graph_is_dominating G Set.univ := by
  intro v
  exact Or.inl (Set.mem_univ v)
