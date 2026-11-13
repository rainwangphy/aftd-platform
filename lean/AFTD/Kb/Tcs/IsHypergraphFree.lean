import AFTD.Prelude

/-!
# is_hypergraph_free

Topic: combinatorics   Node: 46e59e439516

Provenance: formalization of a published result. Source: arXiv:2611.12582 Section 1

A hypergraph H on vertex set Fin n is F-free if there does not exist an embedding f : W ↪ Fin n such that every hyperedge e in F maps under f to an edge in H.
-/

/-- A hypergraph H on Fin n is F-free if there is no injective embedding of the vertices of F into Fin n mapping every edge of F into H. -/
def is_hypergraph_free {W : Type*} {n : ℕ} (H : Finset (Finset (Fin n))) (F : Finset (Finset W)) : Prop := ¬ ∃ f : W ↪ Fin n, ∀ e ∈ F, e.map f ∈ H
