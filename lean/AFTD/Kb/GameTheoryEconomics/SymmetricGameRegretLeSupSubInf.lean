import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SymmetricGameRegret
import AFTD.Kb.GameTheoryEconomics.DotProductMulVecGeInf'

/-!
# symmetric_game_regret_le_sup_sub_inf

Topic: equilibria   Node: 4471f59ba27d

Provenance: helper lemma. arXiv:2610.25524 Lemma 4.1

For any strategy x in stdSimplex ℝ (Fin n), the regret symmetric_game_regret A x is at most the maximum over i of (A *ᵥ x) i minus the minimum over j of (x ᵥ* A) j.
-/

/-- Symmetric game regret is bounded by max pure row payoff minus min pure column payoff. -/
lemma symmetric_game_regret_le_sup_sub_inf {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℝ) (x : stdSimplex ℝ (Fin n)) :
    symmetric_game_regret A x ≤
      Finset.univ.sup' Finset.univ_nonempty (fun i => Matrix.mulVec A x.val i) -
      Finset.univ.inf' Finset.univ_nonempty (fun j => Matrix.vecMul x.val A j) := by
  unfold symmetric_game_regret
  linarith [dotProduct_mulVec_ge_inf' A x]
