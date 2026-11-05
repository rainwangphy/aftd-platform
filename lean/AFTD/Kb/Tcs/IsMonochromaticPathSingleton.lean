import AFTD.Prelude
import AFTD.Kb.Tcs.IsMonochromaticPath
import AFTD.Kb.Tcs.MonoColorSubgraph

/-!
# is_monochromatic_path_singleton

Topic: graphs   Node: 2844d3b3da81

Provenance: helper lemma. arXiv:2611.06362 Section 1

For any types V and C with decidable equality on V and nonempty C, any simple graph G on V, any edge colouring c : G.edgeSet → C, and any vertex v : V, the singleton set {v} is a monochromatic path in G with respect to c.
-/

/-- A single vertex is the vertex set of a trivial monochromatic path. -/
lemma is_monochromatic_path_singleton {V C : Type*} [DecidableEq V] [Nonempty C] (G : SimpleGraph V)
    (c : G.edgeSet → C) (v : V) :
    is_monochromatic_path G c {v} := by
  classical
  refine ⟨Classical.arbitrary C, v, v, SimpleGraph.Walk.nil, ?_, ?_⟩
  · exact SimpleGraph.Walk.IsPath.nil
  · simp
