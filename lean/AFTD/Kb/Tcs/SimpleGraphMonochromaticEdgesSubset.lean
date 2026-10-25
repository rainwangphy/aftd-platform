import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphMonochromaticEdges

/-!
# simple_graph_monochromatic_edges_subset

Topic: combinatorics   Node: 2133641d473b

Provenance: helper lemma. combinatorics/2610-31489-near-optimal-bounds-for-testing-k-colorability.md:160

For any vertex coloring c : V → Fin k of a finite simple graph G on a type V with decidable equality and decidable adjacency, the Finset of monochromatic edges simple_graph_monochromatic_edges G c is a subset of G.edgeFinset.
-/

/-- The Finset of monochromatic edges under any vertex coloring c of G is a subset of G.edgeFinset. -/
theorem simple_graph_monochromatic_edges_subset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (c : V → Fin k) :
    simple_graph_monochromatic_edges G c ⊆ G.edgeFinset :=
  Finset.filter_subset _ _
