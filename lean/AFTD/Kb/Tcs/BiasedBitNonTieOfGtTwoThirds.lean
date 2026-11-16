import AFTD.Prelude
import AFTD.Kb.Tcs.BiasedBitNonTie

/-!
# biased_bit_non_tie_of_gt_two_thirds

Topic: information   Node: 2ac28deaf611

Provenance: helper lemma. arXiv:2611.16066 Cor 5.9

For any bias parameter p satisfying 2 / 3 < p and p < 1, the non-tie condition biased_bit_non_tie p holds.
-/

/-- For any bias parameter p > 2/3, the non-tie condition holds because 2 * a^j < 1 < 1 + a^k for all 1 ≤ j < k. -/
theorem biased_bit_non_tie_of_gt_two_thirds (p : ℝ) (hp : 2 / 3 < p) (hp1 : p < 1) :
    biased_bit_non_tie p := by
  intro j k hj hjk
  set a := (1 - p) / p
  have hp0 : 0 < p := by linarith
  have h1 : 0 < 1 - p := by linarith
  have hpos : 0 < a := div_pos h1 hp0
  have hlt : a < 1 / 2 := by
    rw [div_lt_iff₀ hp0]
    linarith
  have h_le_one : a ≤ 1 := by linarith
  have haj : a ^ j ≤ a := by
    have := pow_le_pow_of_le_one (le_of_lt hpos) h_le_one hj
    simpa using this
  have h_left : 2 * a ^ j < 1 := by
    calc
      2 * a ^ j ≤ 2 * a := by linarith
      _ < 2 * (1 / 2) := by linarith
      _ = 1 := by norm_num
  have h_right : 1 < 1 + a ^ k := by
    have : 0 < a ^ k := pow_pos hpos k
    linarith
  linarith
