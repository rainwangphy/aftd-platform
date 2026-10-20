import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SaddleGapGame
import AFTD.Kb.GameTheoryEconomics.SaddleGapFirstMarginal
import AFTD.Kb.GameTheoryEconomics.SaddleGapSecondMarginal
import AFTD.Kb.GameTheoryEconomics.SaddleGapFirstPayoffPureGeOfSubGe
import AFTD.Kb.GameTheoryEconomics.SaddleGapSelfPayoffGeTwoVOfSubGe
import AFTD.Kb.GameTheoryEconomics.MatrixGameValue
import AFTD.Kb.GameTheoryEconomics.MatrixGameOptimalRowStrategies
import AFTD.Kb.GameTheoryEconomics.MatrixGameGuaranteeI
import AFTD.Kb.GameTheoryEconomics.MatrixGameEj
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.MatrixGamePayoffAgainstColumn

/-!
# saddle_gap_marginal_payoff_bounds

Topic: equilibria   Node: f44b79c46273

Provenance: formalization of a published result. Source: arXiv:2610.25524 Lemma 4.2

Let n be a positive natural number. For any matrix A : Matrix (Fin n) (Fin n) ℝ with non-negative entries and any optimal row strategy σ in `(saddle_gap_game A).optimalRowStrategies`, let a = saddle_gap_first_marginal σ and b = saddle_gap_second_marginal σ in `stdSimplex ℝ (Fin n)`. Then for every k in Fin n, `Matrix.vecMul a.val A k - Matrix.mulVec A b.val k ≥ (saddle_gap_game A).value`, `Matrix.vecMul a.val A k ≥ (saddle_gap_game A).value` for all k in Fin n, and `dotProduct a.val (Matrix.mulVec A a.val) ≥ 2 * (saddle_gap_game A).value`.
-/

lemma saddle_gap_marginal_payoff_bounds_helper_ej {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (σ : stdSimplex ℝ (Fin n × Fin n)) (k : Fin n) :
    (saddle_gap_game A).Ej σ k =
      Matrix.vecMul (saddle_gap_first_marginal σ).val A k -
      Matrix.mulVec A (saddle_gap_second_marginal σ).val k := by
  dsimp [MatrixGame.Ej, MatrixGame.payoffAgainstColumn, saddle_gap_game,
         saddle_gap_first_marginal, saddle_gap_second_marginal,
         Matrix.vecMul, Matrix.mulVec, dotProduct]
  rw [Fintype.sum_prod_type]
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  congr 1
  · congr 1 with i
    rw [Finset.sum_mul]
    rfl
  · rw [Finset.sum_comm]
    congr 1 with j
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm (σ (i, j)) (A k j)

/-- Payoff and self-payoff guarantees from saddle-gap marginal distributions (arXiv:2610.25524 Lemma 4.2). -/
theorem saddle_gap_marginal_payoff_bounds {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (hA_nonneg : ∀ i j, 0 ≤ A i j) (σ : stdSimplex ℝ (Fin n × Fin n)) (hσ : σ ∈ (saddle_gap_game A).optimalRowStrategies) : let a := saddle_gap_first_marginal σ; let b := saddle_gap_second_marginal σ; let v := (saddle_gap_game A).value; (∀ k : Fin n, Matrix.vecMul a.val A k - Matrix.mulVec A b.val k ≥ v) ∧ (∀ k : Fin n, Matrix.vecMul a.val A k ≥ v) ∧ dotProduct a.val (Matrix.mulVec A a.val) ≥ 2 * v := by
  intro a b v
  have h1 : ∀ k : Fin n, Matrix.vecMul a.val A k - Matrix.mulVec A b.val k ≥ v := by
    intro k
    have hopt : (saddle_gap_game A).guarantee_I σ = v := hσ
    rw [← saddle_gap_marginal_payoff_bounds_helper_ej A σ k]
    rw [← hopt]
    dsimp [MatrixGame.guarantee_I]
    apply Finset.inf'_le
    exact Finset.mem_univ k
  have h2 : ∀ k : Fin n, Matrix.vecMul a.val A k ≥ v :=
    saddle_gap_first_payoff_pure_ge_of_sub_ge A hA_nonneg a b v h1
  have h3 : dotProduct a.val (Matrix.mulVec A a.val) ≥ 2 * v :=
    saddle_gap_self_payoff_ge_two_v_of_sub_ge A hA_nonneg a b v h1
  exact ⟨h1, h2, h3⟩
