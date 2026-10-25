import AFTD.Prelude

/-!
# simple_graph_monochromatic_edges

Topic: combinatorics   Node: aadbda1a981d

Provenance: formalization of a published result. Source: combinatorics/2610-31489-near-optimal-bounds-for-testing-k-colorability.md:128

Given a finite type V with decidable equality, a simple graph G on V with decidable adjacency, and a vertex coloring c : V → Fin k, the Finset simple_graph_monochromatic_edges G c consists of all edges e ∈ G.edgeFinset such that (Sym2.map c e).IsDiag.
-/

/-- The Finset of monochromatic edges of a finite simple graph under a vertex coloring c : V → Fin k. -/
def simple_graph_monochromatic_edges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (c : V → Fin k) : Finset (Sym2 V) := G.edgeFinset.filter (fun e => (Sym2.map c e).IsDiag)
