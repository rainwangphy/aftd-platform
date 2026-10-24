import AFTD.Prelude
import AFTD.Kb.Tcs.MonochromaticEdges

/-!
# mem_monochromatic_edges

Topic: combinatorics   Node: a24edf9faf5b

Provenance: helper lemma. arXiv:2610.31489, Section 2

For a finite type V, a simple graph G on V, a natural number k, a coloring c : V → Fin k, and vertices u and v, the unordered pair s(u, v) is in monochromatic_edges G c if and only if G.Adj u v and c u = c v.
-/

/-- Characterization of membership in the set of monochromatic edges. -/
theorem mem_monochromatic_edges {V : Type*} [Fintype V] (G : SimpleGraph V) {k : ℕ} (c : V → Fin k) (u v : V) : s(u, v) ∈ monochromatic_edges G c ↔ G.Adj u v ∧ c u = c v := by
  classical
  unfold monochromatic_edges
  rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Sym2.lift_mk]
