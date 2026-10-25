import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphV3

/-!
# simple_graph_V3_bot

Topic: graphs   Node: 8757f16692f3

Provenance: helper lemma. folklore

In the empty simple graph on a finite type V with decidable equality, the finset of vertices of degree 3 is the empty finset.
-/

/-- The set of degree-3 vertices of an empty graph is empty. -/
theorem simple_graph_V3_bot {V : Type*} [Fintype V] [DecidableEq V] :
    simple_graph_V3 (⊥ : SimpleGraph V) = ∅ := by
  ext v
  simp [simple_graph_V3]
