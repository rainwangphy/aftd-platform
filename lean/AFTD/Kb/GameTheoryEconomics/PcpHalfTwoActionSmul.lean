import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PcpHalfTwoAction

/-!
# pcp_half_two_action_smul

Topic: equilibria   Node: 68c6e1fb6ba4

The closed-form action profile is unchanged when all venue impacts are multiplied by the same nonzero factor.
-/

open Finset in
/-- The closed-form action profile is unchanged when all venue impacts are scaled by the same `t ≠ 0`. -/
lemma pcp_half_two_action_smul {n k : ℕ} (c : Fin n → Fin k → ℝ) (v : Fin k → ℝ) {t : ℝ} (ht : t ≠ 0) :
    pcp_half_two_action c (fun j => t * v j) = pcp_half_two_action c v := by
  funext i j
  simp only [pcp_half_two_action, mul_pow]
  have h4 : t ^ 4 ≠ 0 := pow_ne_zero 4 ht
  have hs : ∑ l, t ^ 4 * v l ^ 4 / c i l = t ^ 4 * ∑ l, v l ^ 4 / c i l := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => mul_div_assoc _ _ _
  rw [hs, show c i j ^ 2 * (t ^ 4 * ∑ l, v l ^ 4 / c i l) = t ^ 4 * (c i j ^ 2 * ∑ l, v l ^ 4 / c i l) by ring,
    mul_div_mul_left _ _ h4]
