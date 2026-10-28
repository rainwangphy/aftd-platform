import AFTD.Prelude
import AFTD.Kb.Tcs.SongBlockVertex

/-!
# song_aux_matching

Topic: combinatorics   Node: 4b260f9f257e

Provenance: helper lemma. step towards admissible_diagonal_selection_isometric_path_cover

The auxiliary perfect matching N of the blocks: in a block that already carries a diagonal of M (ad or bc), take the two horizontal edges ab and cd; in a block carrying no diagonal of M, take the two diagonals ad and bc. This is Table 1 (Section 3.1) of arXiv:2610.33042.
-/

/-- Auxiliary perfect matching N: in a block holding an internal M-diagonal it uses the horizontal pairs {ab, cd}, otherwise the diagonal pairs {ad, bc}. This is Table 1 of Song, arXiv:2610.33042. -/
noncomputable def song_aux_matching (k : ℕ) (M : Finset (Sym2 (Fin (2 * k) × Fin (2 * k)))) : Finset (Sym2 (Fin (2 * k) × Fin (2 * k))) := Finset.univ.biUnion (fun p : Fin k × Fin k =>
    if s(song_block_vertex k p.1 p.2 0 0, song_block_vertex k p.1 p.2 1 1) ∈ M ∨
       s(song_block_vertex k p.1 p.2 0 1, song_block_vertex k p.1 p.2 1 0) ∈ M
    then ({s(song_block_vertex k p.1 p.2 0 0, song_block_vertex k p.1 p.2 0 1),
           s(song_block_vertex k p.1 p.2 1 0, song_block_vertex k p.1 p.2 1 1)} : Finset _)
    else ({s(song_block_vertex k p.1 p.2 0 0, song_block_vertex k p.1 p.2 1 1),
           s(song_block_vertex k p.1 p.2 0 1, song_block_vertex k p.1 p.2 1 0)} : Finset _))
