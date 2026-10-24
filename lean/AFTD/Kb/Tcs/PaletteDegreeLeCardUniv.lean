import AFTD.Prelude
import AFTD.Kb.Tcs.PaletteDegree

/-!
# palette_degree_le_card_univ

Topic: combinatorics   Node: 10f4dbbcf183

Provenance: helper lemma. arXiv:2610.31489, Section 2

For a finite type V, a simple graph G on V, a natural number k, a palette system P : V → Finset (Fin k), a vertex v : V, and a color i : Fin k, the palette degree palette_degree G P v i is at most Fintype.card V.
-/

/-- The palette degree of any vertex is at most the total number of vertices in the graph. -/
theorem palette_degree_le_card_univ {V : Type*} [Fintype V] (G : SimpleGraph V) {k : ℕ} (P : V → Finset (Fin k)) (v : V) (i : Fin k) : palette_degree G P v i ≤ Fintype.card V := by
  unfold palette_degree
  exact le_trans (Finset.card_filter_le _ _) (Finset.card_le_univ _)
