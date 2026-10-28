import AFTD.Prelude

/-!
# song_block_proj

Topic: combinatorics   Node: f50883286b56

Provenance: helper lemma. step towards admissible_diagonal_selection_isometric_path_cover

The block projection pi(r,c) = (r/2, c/2) (integer division) from the (2k)x(2k) grid onto the k x k block grid.
-/

/-- Block index of a grid vertex: each coordinate halved and rounded down. -/
def song_block_proj (k : ℕ) (x : Fin (2 * k) × Fin (2 * k)) : Fin k × Fin k := (⟨x.1.val / 2, by have := x.1.isLt; omega⟩, ⟨x.2.val / 2, by have := x.2.isLt; omega⟩)
