import AFTD.Prelude

/-!
# op_2037_subgraph_fintype

Topic: combinatorics   Node: 92a0a35011d5

Provenance: helper lemma. step towards op_2037_eight_not_extremal

A graph on a finite decidable vertex type has only finitely many subgraphs.
-/

/-- Fintype instance for `G.Subgraph`; Mathlib has none, which is exactly what blocked the earlier fiber count. -/
noncomputable instance op_2037_subgraph_fintype {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Fintype G.Subgraph := Fintype.ofInjective (fun H : G.Subgraph => (H.verts, H.edgeSet)) (by
    intro H₁ H₂ h
    simp only [Prod.mk.injEq] at h
    refine SimpleGraph.Subgraph.ext h.1 (funext fun v => funext fun w => ?_)
    rw [← SimpleGraph.Subgraph.mem_edgeSet, ← SimpleGraph.Subgraph.mem_edgeSet, h.2])
