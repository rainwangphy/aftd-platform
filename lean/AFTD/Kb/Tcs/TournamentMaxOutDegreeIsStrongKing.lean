import AFTD.Prelude
import AFTD.Kb.Tcs.TournamentIsStrongKing
import AFTD.Kb.Tcs.DigraphOutDegree
import AFTD.Kb.Tcs.TournamentStrongKingIffInNeighborOutDegreeLe
import AFTD.Kb.Tcs.DigraphIsTournament

/-!
# tournament_max_out_degree_is_strong_king

Topic: graphs   Node: 1589baa9139d

Provenance: formalization of a published result. Source: arXiv:2610.39702 Lemma 2.5 -- Quantum Query Complexity of Tournament Solutions

In any finite tournament T, every vertex v of maximum out-degree is a strong king.
-/

/-- Every vertex of maximum out-degree in a tournament is a strong king. -/
theorem tournament_max_out_degree_is_strong_king {V : Type*} [Fintype V] (T : Digraph V) [DecidableRel T.Adj] (hT : digraph_is_tournament T) (v : V) (hmax : ∀ u, digraph_out_degree T u ≤ digraph_out_degree T v) : tournament_is_strong_king T v := by
  exact (tournament_strong_king_iff_in_neighbor_out_degree_le T hT v).mpr (fun u _ => hmax u)
