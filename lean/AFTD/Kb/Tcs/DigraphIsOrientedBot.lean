import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphIsOriented

/-!
# digraph_is_oriented_bot

Topic: graphs   Node: 61180b9ebdf7

Provenance: helper lemma. folklore

The empty digraph (⊥ : Digraph V) on any vertex type V is oriented, satisfying digraph_is_oriented (⊥ : Digraph V).
-/

/-- The empty digraph is oriented. -/
theorem digraph_is_oriented_bot (V : Type*) : digraph_is_oriented (⊥ : Digraph V) := by
  simp [digraph_is_oriented]
