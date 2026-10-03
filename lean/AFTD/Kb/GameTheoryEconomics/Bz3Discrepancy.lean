import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PropensityBanzhafIndex
import AFTD.Kb.GameTheoryEconomics.BanzhafDiscrepancy
import AFTD.Kb.GameTheoryEconomics.Bz3Discr
import AFTD.Kb.GameTheoryEconomics.Bz3Pattern
import AFTD.Kb.GameTheoryEconomics.Bz3Measure

/-!
# bz3_discrepancy

Topic: general_equilibrium   Node: d77da8763fde

For three players and p = q = 1/2, the discrepancy for target (3/10, 7/10, 0) equals the rational discrepancy of the winning pattern.
-/

lemma bz3_discrepancy (w : Fin 3 → ℝ) :
    banzhaf_discrepancy ![3 / 10, 7 / 10, 0] (1 / 2) (1 / 2) w = (bz3_discr (bz3_pattern w) : ℝ) := by
  unfold banzhaf_discrepancy propensity_banzhaf_index bz3_discr
  simp only [bz3_measure, Fin.sum_univ_three]
  have h4 : ∀ a b : ℝ, (a / 4) / b = a / (4 * b) := fun a b => by rw [div_div]
  rw [← add_div, ← add_div]
  simp only [div_div_div_cancel_right₀ (show (4 : ℝ) ≠ 0 by norm_num)]
  push_cast
  simp
