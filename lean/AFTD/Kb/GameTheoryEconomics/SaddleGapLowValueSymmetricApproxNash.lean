import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SaddleGapGame
import AFTD.Kb.GameTheoryEconomics.SymmetricGameRegret
import AFTD.Kb.GameTheoryEconomics.MatrixGameOptimalColumnStrategies
import AFTD.Kb.GameTheoryEconomics.MatrixGameValue
import AFTD.Kb.GameTheoryEconomics.SaddleGapGuaranteeIILeOfMemOptimalColumnStrategies
import AFTD.Kb.GameTheoryEconomics.SaddleGapGuaranteeIIEqSupSubInf
import AFTD.Kb.GameTheoryEconomics.SymmetricGameRegretLeOfSupSubInfLe
import AFTD.Kb.GameTheoryEconomics.MatrixGameGuaranteeII

/-!
# saddle_gap_low_value_symmetric_approx_nash

Topic: equilibria   Node: 0ae69fde0f21

Provenance: formalization of a published result. Source: arXiv:2610.25524 Lemma 4.1

Let n be a positive natural number with `[NeZero n]`. Let A : Matrix (Fin n) (Fin n) ℝ be an n-by-n real matrix with entries in [0, 1] (satisfying `∀ i j, 0 ≤ A i j` and `∀ i j, A i j ≤ 1`). Let ε be a real number. If x : stdSimplex ℝ (Fin n) is an optimal column strategy for the saddle-gap game (that is, `x ∈ (saddle_gap_game A).optimalColumnStrategies`) and the value of the saddle-gap game satisfies `(saddle_gap_game A).value ≤ ε`, then the symmetric game regret of x satisfies `symmetric_game_regret A x ≤ ε`.
-/

/-- If the saddle-gap game has value at most ε, an optimal column strategy yields a symmetric ε-approximate Nash equilibrium (regret at most ε). -/
theorem saddle_gap_low_value_symmetric_approx_nash {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA_nonneg : ∀ i j, 0 ≤ A i j) (hA_le_one : ∀ i j, A i j ≤ 1)
    (ε : ℝ) (x : stdSimplex ℝ (Fin n))
    (hx : x ∈ (saddle_gap_game A).optimalColumnStrategies)
    (hv : (saddle_gap_game A).value ≤ ε) :
    symmetric_game_regret A x ≤ ε := by
  have h1 : (saddle_gap_game A).guarantee_II x ≤ (saddle_gap_game A).value :=
    saddle_gap_guarantee_II_le_of_mem_optimalColumnStrategies A x hx
  have h2 : (saddle_gap_game A).guarantee_II x ≤ ε := le_trans h1 hv
  rw [saddle_gap_guarantee_II_eq_sup_sub_inf] at h2
  exact symmetric_game_regret_le_of_sup_sub_inf_le A x ε h2
