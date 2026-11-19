import AFTD.Prelude
import AFTD.Kb.Tcs.ClosedNetworkParityBound

/-!
# closed_network_parity_bound_le_sqrt_two

Topic: quantum   Node: aca42214ca72

Provenance: helper lemma. step towards open_problem_735_parity_bound_higher_dimension

For any natural number n ≥ 1, the closed network parity bound 2^(1/2 - 1/(2n)) is at most Real.sqrt 2.
-/

/-- For any natural number n ≥ 1, the closed network parity bound 2^(1/2 - 1/(2n)) is at most Real.sqrt 2. -/
theorem closed_network_parity_bound_le_sqrt_two (n : ℕ) (hn : 1 ≤ n) :
    closed_network_parity_bound n ≤ Real.sqrt 2 := by
  unfold closed_network_parity_bound
  rw [Real.sqrt_eq_rpow]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hden : (0 : ℝ) < 2 * (n : ℝ) := by positivity
  have : 0 ≤ 1 / (2 * (n : ℝ)) := by positivity
  linarith
