import AFTD.Prelude

/-!
# palette_degree

Topic: combinatorics   Node: 1b63104284d9

Provenance: formalization of a published result. Source: arXiv:2610.31489, Section 2

Given a finite type V, a simple graph G on V, a natural number k, a palette system P : V → Finset (Fin k), a vertex v : V, and a color i : Fin k, palette_degree G P v i is the cardinality of the Finset of neighbors u in G.neighborFinset v such that i ∈ P u.
-/

/-- The palette degree of a vertex for a given color in a palette system. -/
noncomputable def palette_degree {V : Type*} [Fintype V] (G : SimpleGraph V) {k : ℕ} (P : V → Finset (Fin k)) (v : V) (i : Fin k) : ℕ := by classical exact ((G.neighborFinset v).filter (fun u => i ∈ P u)).card
