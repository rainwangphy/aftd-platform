import AFTD.Prelude

/-!
# palette_active_vertices

Topic: combinatorics   Node: 2e638476c045

Provenance: formalization of a published result. Source: arXiv:2610.31489, Section 2

Given a finite type V, a natural number k, and a palette system P : V → Finset (Fin k), palette_active_vertices P is the Finset of all vertices v : V such that P v ≠ ∅.
-/

/-- The set of active vertices of a palette system, having nonempty palette. -/
noncomputable def palette_active_vertices {V : Type*} [Fintype V] {k : ℕ} (P : V → Finset (Fin k)) : Finset V := by classical exact Finset.univ.filter (fun v => P v ≠ ∅)
