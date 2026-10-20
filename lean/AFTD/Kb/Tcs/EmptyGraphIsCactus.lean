import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsCactus

/-!
# empty_graph_is_cactus

Topic: automata   Node: bad3b6720c09

Provenance: helper lemma. folklore

The edgeless graph on any vertex type is a cactus graph.
-/

/-- The empty graph on any vertex type is a cactus graph. -/
theorem empty_graph_is_cactus (V : Type*) :
    simple_graph_is_cactus (⊥ : SimpleGraph V) := by
  unfold simple_graph_is_cactus
  intro u₁ u₂ p₁ p₂ hp₁ hp₂ h
  cases p₁ with
  | nil => simp at h
  | cons hadj p => simp at hadj
