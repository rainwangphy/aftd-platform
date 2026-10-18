import AFTD.Prelude

/-!
# five_diamond_level_coloring

Topic: combinatorics   Node: b9dc488320a7

Provenance: helper lemma. step towards op_270_five_diamond_poset_ramsey_number

For k ≥ 1, the colouring of the subsets of Fin d that sends A to the minimum of k-1 and |A| divided by 4 (as an element of Fin k).
-/

/-- The level colouring A ↦ min (k-1) (|A|/4) with k colours on the subsets of Fin d, used to show R_k(D_5) > d whenever d ≤ 4k-1. -/
def five_diamond_level_coloring (k d : ℕ) (hk : 1 ≤ k) (A : Finset (Fin d)) : Fin k := ⟨min (k - 1) (A.card / 4), lt_of_le_of_lt (min_le_left _ _) (by omega)⟩
