import AFTD.Prelude

/-!
# song_corner_label

Topic: combinatorics   Node: 344a03c42b57

Provenance: helper lemma. step towards admissible_diagonal_selection_isometric_path_cover

The label of a grid vertex inside its block, given by its two coordinate parities: (r mod 2, c mod 2), so that a = (0,0), b = (0,1), c = (1,0), d = (1,1).
-/

/-- Label a/b/c/d of a grid vertex inside its block, as the pair of coordinate parities. -/
def song_corner_label (k : ℕ) (x : Fin (2 * k) × Fin (2 * k)) : Fin 2 × Fin 2 := (⟨x.1.val % 2, by have := x.1.isLt; omega⟩, ⟨x.2.val % 2, by have := x.2.isLt; omega⟩)
