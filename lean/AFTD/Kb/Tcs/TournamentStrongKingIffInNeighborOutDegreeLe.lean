import AFTD.Prelude
import AFTD.Kb.Tcs.TournamentIsStrongKing
import AFTD.Kb.Tcs.DigraphOutDegree
import AFTD.Kb.Tcs.TournamentTwoPathDiffEqOutDegreeDiff
import AFTD.Kb.Tcs.DigraphTwoPathCount
import AFTD.Kb.Tcs.DigraphIsTournament

/-!
# tournament_strong_king_iff_in_neighbor_out_degree_le

Topic: graphs   Node: 11d78ad6f599

Provenance: formalization of a published result. Source: arXiv:2610.39702 Lemma 2.4 -- Quantum Query Complexity of Tournament Solutions

In any finite tournament T, a vertex v is a strong king if and only if every in-neighbor u of v (that is, every vertex u with an arc from u to v) satisfies d⁺(u) ≤ d⁺(v).
-/

/-- A vertex in a finite tournament is a strong king if and only if every in-neighbor has out-degree at most its out-degree. -/
theorem tournament_strong_king_iff_in_neighbor_out_degree_le {V : Type*} [Fintype V] (T : Digraph V) [DecidableRel T.Adj] (hT : digraph_is_tournament T) (v : V) : tournament_is_strong_king T v ↔ ∀ u, T.Adj u v → digraph_out_degree T u ≤ digraph_out_degree T v := by
  classical
  constructor
  · intro hk u huv
    have h := tournament_two_path_diff_eq_out_degree_diff T hT huv
    have h' : (digraph_two_path_count T u v : ℤ) < (digraph_two_path_count T v u : ℤ) := by
      exact_mod_cast hk u huv
    have h2 : (digraph_out_degree T u : ℤ) ≤ (digraph_out_degree T v : ℤ) := by omega
    exact_mod_cast h2
  · intro hk u huv
    have h := tournament_two_path_diff_eq_out_degree_diff T hT huv
    have h2 : (digraph_out_degree T u : ℤ) ≤ (digraph_out_degree T v : ℤ) := by
      exact_mod_cast hk u huv
    have h3 : (digraph_two_path_count T u v : ℤ) < (digraph_two_path_count T v u : ℤ) := by omega
    exact_mod_cast h3
