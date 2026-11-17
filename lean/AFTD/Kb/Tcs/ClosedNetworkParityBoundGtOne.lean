import AFTD.Prelude
import AFTD.Kb.Tcs.ClosedNetworkParityBound

/-!
# closed_network_parity_bound_gt_one

Topic: quantum   Node: 13aa68760c02

Provenance: helper lemma. step towards open_problem_735_parity_bound_higher_dimension

For any n ≥ 3, the closed network parity bound 2^(1/2 - 1/(2n)) is strictly greater than 1.
-/

/-- For any n ≥ 3, the closed network parity bound 2^(1/2 - 1/(2n)) is strictly greater than 1. -/
theorem closed_network_parity_bound_gt_one (n : ℕ) (hn : 3 ≤ n) :
    1 < closed_network_parity_bound n := by
  change 1 < (2 : ℝ) ^ ((1 : ℝ) / 2 - 1 / (2 * (n : ℝ)))
  apply Real.one_lt_rpow (by norm_num)
  have hn_real : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpos : (0 : ℝ) < 2 * (n : ℝ) := by linarith
  have hrecip : 1 / (2 * (n : ℝ)) ≤ (1 : ℝ) / 6 := by
    rw [one_div_le_one_div hpos (by norm_num)]
    linarith
  linarith
