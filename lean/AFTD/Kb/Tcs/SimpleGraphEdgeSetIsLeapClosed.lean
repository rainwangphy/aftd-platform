import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsLeapClosed
import AFTD.Kb.Tcs.SimpleGraphLeapGroup

/-!
# simple_graph_edgeSet_is_leap_closed

Topic: graphs   Node: 973c470e0bab

Provenance: helper lemma. arXiv:2610.18463 Question 5.9

For any simple graph G, its full edge set E(G) is leap-closed.
-/

/-- The ground edge set of a simple graph is leap-closed. -/
theorem simple_graph_edgeSet_is_leap_closed {V : Type*} (G : SimpleGraph V) :
    simple_graph_is_leap_closed G G.edgeSet := by
  refine ⟨subset_rfl, ?_⟩
  intro e he
  exact False.elim (he.2 he.1)
