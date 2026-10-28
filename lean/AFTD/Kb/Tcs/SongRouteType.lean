import AFTD.Prelude
import AFTD.Kb.Tcs.SongBlockProj
import AFTD.Kb.Tcs.SongCornerLabel
import AFTD.Kb.Tcs.SongBlockVertex

/-!
# song_route_type

Topic: combinatorics   Node: 79bd89adf840

Provenance: helper lemma. step towards admissible_diagonal_selection_isometric_path_cover

The type (A = true, B = false) of the local route of a vertex, as in Table 1 of arXiv:2610.33042: a block holding the internal M-diagonal ad carries a single route c-d-a-b of type B; a block holding the internal M-diagonal bc carries a single route a-b-c-d of type A; a block holding neither carries the type A route a-d and the type B route c-b, so a and d are type A and b and c are type B.
-/

/-- Type of the local route through a vertex: `true` = type A (ports a,d) and `false` = type B (ports c,b), read off from the block's internal M-diagonal and the vertex's corner label. -/
def song_route_type (k : ℕ) (M : Finset (Sym2 (Fin (2 * k) × Fin (2 * k)))) (x : Fin (2 * k) × Fin (2 * k)) : Bool := let p := song_block_proj k x
   if s(song_block_vertex k p.1 p.2 0 0, song_block_vertex k p.1 p.2 1 1) ∈ M then false
   else if s(song_block_vertex k p.1 p.2 0 1, song_block_vertex k p.1 p.2 1 0) ∈ M then true
   else decide ((song_corner_label k x).1 = (song_corner_label k x).2)
