import AFTD.Prelude
import AFTD.Kb.Tcs.TournamentMinRank
import AFTD.Kb.Tcs.DigraphFlipByMatrixZero
import AFTD.Kb.Tcs.DigraphIsAcyclic
import AFTD.Kb.Tcs.DigraphFlipByMatrix

/-!
# tournament_min_rank_eq_zero_of_is_acyclic

Topic: graphs   Node: a612da6656c9

Provenance: helper lemma. Sanity lemma for tournament_min_rank (arXiv:2610.13798, Sec. 2.2).

An acyclic digraph has tournament minimum rank 0 (the zero matrix decycles it).
-/

theorem tournament_min_rank_eq_zero_of_is_acyclic {V : Type*} [Fintype V] (D : Digraph V)
    (h : digraph_is_acyclic D) : tournament_min_rank D = 0 := by
  apply Nat.sInf_eq_zero.mpr
  left
  exact ⟨0, Matrix.isSymm_zero, by rwa [digraph_flip_by_matrix_zero], Matrix.rank_zero⟩
