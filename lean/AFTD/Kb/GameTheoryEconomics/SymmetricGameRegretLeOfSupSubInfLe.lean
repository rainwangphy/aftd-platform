import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SymmetricGameRegret
import AFTD.Kb.GameTheoryEconomics.SymmetricGameRegretLeSupSubInf

/-!
# symmetric_game_regret_le_of_sup_sub_inf_le

Topic: equilibria   Node: 27725169d118

Provenance: helper lemma. arXiv:2610.25524, Lemma 4.1

For a positive natural number n, an n-by-n real matrix A, a strategy x in `stdSimplex ℝ (Fin n)`, and a real number ε, if `Finset.univ.sup' Finset.univ_nonempty (fun i => Matrix.mulVec A x.val i) - Finset.univ.inf' Finset.univ_nonempty (fun j => Matrix.vecMul x.val A j) ≤ ε`, then `symmetric_game_regret A x ≤ ε`.
-/

/-- If the maximum pure row payoff minus minimum pure column payoff is at most ε, then the symmetric game regret is at most ε. -/
lemma symmetric_game_regret_le_of_sup_sub_inf_le {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℝ) (x : stdSimplex ℝ (Fin n)) (ε : ℝ)
    (h : Finset.univ.sup' Finset.univ_nonempty (fun i => Matrix.mulVec A x.val i) -
         Finset.univ.inf' Finset.univ_nonempty (fun j => Matrix.vecMul x.val A j) ≤ ε) :
    symmetric_game_regret A x ≤ ε := by
  exact le_trans (symmetric_game_regret_le_sup_sub_inf A x) h
