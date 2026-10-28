import AFTD.Prelude
import AFTD.Kb.Tcs.SongAuxMatching

/-!
# song_edge_graph

Topic: combinatorics   Node: 4dab1141c671

Provenance: helper lemma. step towards admissible_diagonal_selection_isometric_path_cover

The alternating graph H = (V_{2k-1}, M ∪ N) on the (2k)x(2k) grid vertices, whose edges are the selected diagonals together with the auxiliary matching N of the blocks.
-/

/-- Alternating graph H = (V_{2k-1}, M ∪ N) whose edges are the admissible diagonals together with the auxiliary matching. -/
noncomputable def song_edge_graph (k : ℕ) (M : Finset (Sym2 (Fin (2 * k) × Fin (2 * k)))) : SimpleGraph (Fin (2 * k) × Fin (2 * k)) := SimpleGraph.fromEdgeSet ((M ∪ song_aux_matching k M : Finset _) : Set _)
