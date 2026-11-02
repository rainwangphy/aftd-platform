import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphCommonPredecessorGraph

/-!
# digraph_common_predecessor_graph_connected

Topic: graphs   Node: 068d9682eed0

Provenance: helper lemma. Connectivity refinement of the auxiliary-graph argument for OP-110.

In a nonempty loopless strongly connected digraph in which every arc has a common in-neighbor, the common-predecessor graph is connected.
-/

theorem digraph_common_predecessor_graph_connected
    (α : Type) [Nonempty α] (D : Digraph α)
    (hloop : ∀ v, ¬ D.Adj v v)
    (hdom : ∀ u v, D.Adj u v → ∃ w, D.Adj w u ∧ D.Adj w v)
    (hstrong : ∀ u v, Relation.ReflTransGen D.Adj u v) :
    (digraph_common_predecessor_graph D).Connected := by
  apply SimpleGraph.Connected.mk
  intro u v
  apply ((digraph_common_predecessor_graph D).reachable_iff_reflTransGen u v).2
  have hsub : D.Adj ≤ (digraph_common_predecessor_graph D).Adj := by
    intro x y hxy
    obtain ⟨w, hwx, hwy⟩ := hdom x y hxy
    refine ⟨?_, w, hwx, hwy⟩
    intro h
    subst y
    exact hloop x hxy
  exact (Relation.ReflTransGen.mono hsub) u v (hstrong u v)
