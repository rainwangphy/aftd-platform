import AFTD.Prelude

/-!
# song_block_vertex

Topic: combinatorics   Node: c7f988e6ec1a

Provenance: helper lemma. step towards admissible_diagonal_selection_isometric_path_cover

Corner (u,v) of the 2x2 block B_{ij} of the (2k)x(2k) grid: song_block_vertex k i j u v = (2i+u, 2j+v). With (u,v) = (0,0),(0,1),(1,0),(1,1) these are the paper's corners a, b, c, d of the block.
-/

/-- Corner (u,v) of the 2x2 block (i,j) of the (2k)x(2k) grid, i.e. the vertex (2i+u, 2j+v). -/
def song_block_vertex (k : ℕ) (i j : Fin k) (u v : Fin 2) : Fin (2 * k) × Fin (2 * k) := (⟨2 * i.val + u.val, by have := i.isLt; have := u.isLt; omega⟩,
    ⟨2 * j.val + v.val, by have := j.isLt; have := v.isLt; omega⟩)
