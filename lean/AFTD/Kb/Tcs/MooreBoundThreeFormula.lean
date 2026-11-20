import AFTD.Prelude
import AFTD.Kb.Tcs.MooreBound
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# moore_bound_three_formula

Topic: graphs   Node: 69b1b1dac94b

Provenance: helper lemma. arXiv:2611.26037 Sec. 1

For any integer d ≥ 1, the Moore bound for diameter 3 evaluates to m(d, 3) = d^3 - d^2 + d + 1.
-/

/-- Algebraic expansion of the Moore bound m(d, 3) = d^3 - d^2 + d + 1 for d >= 1. -/
theorem moore_bound_three_formula (d : ℕ) (hd : 1 ≤ d) : moore_bound d 3 = d ^ 3 - d ^ 2 + d + 1 := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hd
  simp only [moore_bound, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  have hle : (1 + e) ^ 2 ≤ (1 + e) ^ 3 := by nlinarith [Nat.zero_le e]
  have h : (1 + e) ^ 3 - (1 + e) ^ 2 = (1 + e) ^ 2 * e := by
    rw [Nat.sub_eq_iff_eq_add hle]
    ring
  rw [h]
  ring
