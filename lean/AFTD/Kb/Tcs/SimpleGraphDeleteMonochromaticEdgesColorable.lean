import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphMonochromaticEdges

/-!
# simple_graph_delete_monochromatic_edges_colorable

Topic: combinatorics   Node: 0ba41af79261

Provenance: helper lemma. combinatorics/2610-31489-near-optimal-bounds-for-testing-k-colorability.md:160

For any vertex coloring c : V → Fin k of a finite simple graph G on a type V with decidable equality and decidable adjacency, deleting the Finset of monochromatic edges simple_graph_monochromatic_edges G c from G leaves a k-colorable graph.
-/

/-- Deleting all monochromatic edges under a vertex coloring c makes the remaining graph k-colorable. -/
theorem simple_graph_delete_monochromatic_edges_colorable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (c : V → Fin k) :
    (G.deleteEdges (simple_graph_monochromatic_edges G c : Set (Sym2 V))).Colorable k := by
  refine ⟨SimpleGraph.Coloring.mk c ?_⟩
  intro v w hvw
  rw [SimpleGraph.deleteEdges_adj] at hvw
  rcases hvw with ⟨hadj, hnotmem⟩
  intro heq
  apply hnotmem
  change s(v, w) ∈ simple_graph_monochromatic_edges G c
  rw [simple_graph_monochromatic_edges, Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  · rw [Sym2.map_mk, Sym2.mk_isDiag_iff]
    exact heq
