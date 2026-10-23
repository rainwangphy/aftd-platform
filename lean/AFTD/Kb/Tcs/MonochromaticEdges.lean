import AFTD.Prelude

/-!
# monochromatic_edges

Topic: combinatorics   Node: 5a13f3fbf008

Provenance: formalization of a published result. Source: arXiv:2610.31489, Section 2

Given a finite type V, a simple graph G on V, a natural number k, and a coloring c : V → Fin k, monochromatic_edges G c is defined as the Finset of edges e in G.edgeFinset whose endpoints have the same color under c, filtered via Sym2.lift.
-/

/-- The finset of monochromatic edges of a graph under a vertex coloring. -/
noncomputable def monochromatic_edges {V : Type*} [Fintype V] (G : SimpleGraph V) {k : ℕ} (c : V → Fin k) : Finset (Sym2 V) := by classical exact G.edgeFinset.filter (fun e => Sym2.lift ⟨fun u v => c u = c v, fun _ _ => propext eq_comm⟩ e)
