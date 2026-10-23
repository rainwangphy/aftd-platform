import AFTD.Prelude
import AFTD.Kb.Tcs.MonoColorSubgraph

/-!
# mono_color_subgraph_le

Topic: graphs   Node: b14483dd6738

Provenance: helper lemma. arXiv:2610.29813

The monochromatic subgraph of G in colour col is a subgraph of G.
-/

/-- Every monochromatic subgraph of G is a subgraph of G. -/
theorem mono_color_subgraph_le {V C : Type*} (G : SimpleGraph V) (c : G.edgeSet → C) (col : C) :
    mono_color_subgraph G c col ≤ G := by
  intro u v h
  rw [mono_color_subgraph, SimpleGraph.fromEdgeSet_adj] at h
  obtain ⟨hedge, -⟩ := h.1
  exact hedge
