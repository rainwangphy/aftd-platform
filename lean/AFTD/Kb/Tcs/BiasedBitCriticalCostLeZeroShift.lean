import AFTD.Prelude
import AFTD.Kb.Tcs.BiasedBitCriticalCost

/-!
# biased_bit_critical_cost_le_zero_shift

Topic: information   Node: 73e1113b21d1

Provenance: helper lemma. arXiv:2611.16066 Thm 5.4

For any bias parameter p satisfying 1 / 2 < p and p < 1, the critical cost biased_bit_critical_cost p is at most ((1 - p) / p) / (1 - (1 - p) / p).
-/

/-- The critical cost c_crit(p) is at most the shift l = 0 evaluation a / (1 - a). -/
theorem biased_bit_critical_cost_le_zero_shift (p : ℝ) (hp : 1 / 2 < p) (hp1 : p < 1) :
    biased_bit_critical_cost p ≤ ((1 - p) / p) / (1 - (1 - p) / p) := by
  unfold biased_bit_critical_cost
  let a := (1 - p) / p
  have hp0 : 0 < p := by linarith
  have ha0 : 0 < a := div_pos (by linarith) hp0
  have ha1 : a < 1 := by
    rw [div_lt_one hp0]
    linarith
  have h1a : 0 < 1 - a := by linarith
  have hbdd : BddBelow (Set.range fun (l : ℕ) => (l : ℝ) + a * (2 * a ^ l - 1) / (1 - a)) := by
    use (-a / (1 - a))
    rintro x ⟨l, rfl⟩
    dsimp
    have hl : 0 ≤ (l : ℝ) := Nat.cast_nonneg l
    have hal : 0 ≤ a ^ l := pow_nonneg (le_of_lt ha0) l
    have h_frac : -a / (1 - a) ≤ a * (2 * a ^ l - 1) / (1 - a) := by
      rw [div_le_div_iff_of_pos_right h1a]
      nlinarith
    linarith
  have hmem : a / (1 - a) ∈ Set.range (fun (l : ℕ) => (l : ℝ) + a * (2 * a ^ l - 1) / (1 - a)) := by
    use 0
    dsimp
    ring
  exact csInf_le hbdd hmem
