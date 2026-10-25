import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphMonochromaticEdges

/-!
# simple_graph_exists_monochromatic_edges_subset_of_delete_edges_colorable

Topic: combinatorics   Node: 57add4369f66

Provenance: helper lemma. combinatorics/2610-31489-near-optimal-bounds-for-testing-k-colorability.md:160

For any finite simple graph G on a type V with decidable equality and decidable adjacency, and any Finset E' of edges of Sym2 V such that deleting E' from G leaves a k-colorable graph, there exists a vertex coloring c : V → Fin k such that simple_graph_monochromatic_edges G c is a subset of E'.
-/

/-- If deleting an edge Finset E' makes G k-colorable, then some vertex coloring has all its monochromatic edges contained in E'. -/
theorem simple_graph_exists_monochromatic_edges_subset_of_delete_edges_colorable
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} {E' : Finset (Sym2 V)} (hc : (G.deleteEdges (E' : Set (Sym2 V))).Colorable k) :
    ∃ c : V → Fin k, simple_graph_monochromatic_edges G c ⊆ E' := by
  rcases hc with ⟨col⟩
  refine ⟨col, ?_⟩
  intro e he
  rw [simple_graph_monochromatic_edges, Finset.mem_filter] at he
  rcases he with ⟨heG, hdiag⟩
  rw [SimpleGraph.mem_edgeFinset] at heG
  induction' e using Sym2.ind with v w
  rw [Sym2.map_mk, Sym2.mk_isDiag_iff] at hdiag
  by_contra hnot
  have hE' : s(v, w) ∉ (E' : Set (Sym2 V)) := by
    intro hmem
    apply hnot
    exact Finset.mem_coe.mp hmem
  have hadj : (G.deleteEdges (E' : Set (Sym2 V))).Adj v w := by
    rw [SimpleGraph.deleteEdges_adj]
    exact ⟨heG, hE'⟩
  have hne := col.valid hadj
  exact hne hdiag
