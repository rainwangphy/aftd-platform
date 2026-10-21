import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SaddleGapGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameOptimalColumnStrategies
import AFTD.Kb.GameTheoryEconomics.MatrixGameGuaranteeII
import AFTD.Kb.GameTheoryEconomics.MatrixGameValue

/-!
# saddle_gap_guarantee_II_le_of_mem_optimalColumnStrategies

Topic: equilibria   Node: ea75af0ebb93

Provenance: helper lemma. arXiv:2610.25524, Section 4

For a positive natural number n, an n-by-n real matrix A, and a strategy x in `stdSimplex ℝ (Fin n)`, if x is an optimal column strategy in `(saddle_gap_game A).optimalColumnStrategies`, then Player II's guarantee `(saddle_gap_game A).guarantee_II x` is at most the value `(saddle_gap_game A).value`.
-/

/-- Player II's guarantee against any optimal column strategy in the saddle-gap game is at most the game's value. -/
lemma saddle_gap_guarantee_II_le_of_mem_optimalColumnStrategies {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℝ) (x : stdSimplex ℝ (Fin n))
    (hx : x ∈ (saddle_gap_game A).optimalColumnStrategies) :
    (saddle_gap_game A).guarantee_II x ≤ (saddle_gap_game A).value := by
  exact hx.le
