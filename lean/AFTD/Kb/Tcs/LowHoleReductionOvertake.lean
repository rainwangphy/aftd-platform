import AFTD.Prelude
import AFTD.Kb.Tcs.RecursiveLineHoleBudget
import AFTD.Kb.Tcs.LowHoleTwoMulSubGeTwo
import AFTD.Kb.Tcs.LowHoleReductionForcesZero
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# low_hole_reduction_overtake

Topic: combinatorics   Node: c7a1496e319f

Provenance: helper lemma. scout/2610-22875-overtake-and-the-recursive-line-equality-for-second-order-z.md:549

Let m, n be natural numbers and let z, z_RL, z_2, z_2A, H, d be integers. If z_RL ≤ z_2, z_2 ≤ z_2A, 0 ≤ H, 0 ≤ d, 2 * (z_2A - z_RL) = recursive_line_hole_budget m n z z_RL - H - d, (d = 0 → z_2A ≤ z_2), and recursive_line_hole_budget m n z z_RL ≤ 2, then z_2A = z_2.
-/

/-- Low-hole reduction ruling out overtake for given hole count and deficit. -/
theorem low_hole_reduction_overtake
    (m n : ℕ) (z z_RL z_2 z_2A H d : ℤ)
    (hle : z_RL ≤ z_2)
    (h_overtake : z_2 ≤ z_2A)
    (hH : 0 ≤ H)
    (hd : 0 ≤ d)
    (h_budget : 2 * (z_2A - z_RL) = recursive_line_hole_budget m n z z_RL - H - d)
    (h_limited : d = 0 → z_2A ≤ z_2)
    (h_low : recursive_line_hole_budget m n z z_RL ≤ 2) :
    z_2A = z_2 := by
  by_contra hne
  have hgt : z_2 < z_2A := lt_of_le_of_ne h_overtake (Ne.symm hne)
  have h2 : 2 ≤ 2 * (z_2A - z_RL) := low_hole_two_mul_sub_ge_two z_RL z_2 z_2A hle hgt
  have hzero := low_hole_reduction_forces_zero (2 * (z_2A - z_RL))
    (recursive_line_hole_budget m n z z_RL) H d hH hd h_budget h2 h_low
  have hd0 : d = 0 := hzero.2.2
  have hle' : z_2A ≤ z_2 := h_limited hd0
  linarith
