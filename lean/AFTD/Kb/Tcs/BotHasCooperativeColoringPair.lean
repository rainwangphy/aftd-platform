import AFTD.Prelude
import AFTD.Kb.Tcs.HasCooperativeColoringPair

/-!
# bot_has_cooperative_coloring_pair

Topic: combinatorics   Node: 59753b29a556

Provenance: helper lemma. folklore

Two empty (edgeless) graphs on any vertex set admit a cooperative coloring.
-/

/-- Two empty graphs on any vertex set admit a cooperative coloring. -/
theorem bot_has_cooperative_coloring_pair {V : Type*} :
    has_cooperative_coloring_pair (⊥ : SimpleGraph V) (⊥ : SimpleGraph V) := by
  refine ⟨Set.univ, Set.univ, ?_, ?_, ?_⟩
  · intro x _ y _ _
    exact (SimpleGraph.bot_adj x y).mp
  · intro x _ y _ _
    exact (SimpleGraph.bot_adj x y).mp
  · simp
