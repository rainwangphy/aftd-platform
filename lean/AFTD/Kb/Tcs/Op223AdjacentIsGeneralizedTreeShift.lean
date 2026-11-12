import AFTD.Prelude
import AFTD.Kb.Tcs.GtsGraph
import AFTD.Kb.Tcs.IsGeneralizedTreeShift

/-!
# op223_adjacent_is_generalized_tree_shift

Topic: graphs   Node: 0a3be77b9402

Provenance: helper lemma. step towards nonsustainable_tree_has_nonsustainable_successor_closer_to_star

For any tree T and any adjacent vertices u, v, the graph gts_graph T u v u obtained by shifting all neighbours of v other than u to u is a generalized tree shift of T.
-/

open SimpleGraph

/-- For any tree T and any adjacent vertices u, v, the graph gts_graph T u v u obtained by shifting all neighbours of v other than u to u is a generalized tree shift of T. -/
theorem op223_adjacent_is_generalized_tree_shift {V : Type*}
  (T : SimpleGraph V) (hT : T.IsTree) (u v : V) (huv : T.Adj u v) :
  is_generalized_tree_shift T (gts_graph T u v u) := by
  refine ⟨hT, u, v, SimpleGraph.Walk.cons huv SimpleGraph.Walk.nil, ?_, huv.ne, ?_, ?_⟩
  · exact SimpleGraph.Walk.IsPath.nil.cons (by simpa using huv.ne)
  · intro x hx hxu hxv
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> contradiction
  · rfl
