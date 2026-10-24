import AFTD.Prelude
import AFTD.Kb.Tcs.PaletteActiveVertices

/-!
# mem_palette_active_vertices

Topic: combinatorics   Node: ee7d502b5a5e

Provenance: helper lemma. arXiv:2610.31489, Section 2

For a finite type V, a natural number k, a palette system P : V → Finset (Fin k), and a vertex v : V, v is in palette_active_vertices P if and only if P v ≠ ∅.
-/

/-- Characterization of active vertices in a palette system. -/
theorem mem_palette_active_vertices {V : Type*} [Fintype V] {k : ℕ} (P : V → Finset (Fin k)) (v : V) : v ∈ palette_active_vertices P ↔ P v ≠ ∅ := by simp [palette_active_vertices]
