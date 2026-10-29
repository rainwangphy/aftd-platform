import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphIsSemicompleteMultipartite

/-!
# digraph_bot_is_semicomplete_multipartite

Topic: graphs   Node: 98f46e2c667c

Provenance: helper lemma. folklore

The empty digraph on any vertex type is semicomplete multipartite.
-/

/-- The empty digraph is semicomplete multipartite. -/
theorem digraph_bot_is_semicomplete_multipartite {V : Type*} :
    digraph_is_semicomplete_multipartite (⊥ : Digraph V) := by
  refine ⟨fun v => by simp, ?_⟩
  unfold SimpleGraph.IsCompleteMultipartite
  refine ⟨fun a b c hab _ => ?_⟩
  simpa using hab
