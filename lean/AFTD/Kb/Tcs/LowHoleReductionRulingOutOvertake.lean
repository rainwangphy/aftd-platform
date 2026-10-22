import AFTD.Prelude
import AFTD.Kb.Tcs.RecursiveLineHoleBudget
import AFTD.Kb.Tcs.LowHoleReductionOvertake

/-!
# low_hole_reduction_ruling_out_overtake

Topic: combinatorics   Node: a1c2457457a8

Provenance: formalization of a published result. Source: scout/2610-22875-overtake-and-the-recursive-line-equality-for-second-order-z.md:539

Let m, n be natural numbers and let z, z_RL, z_2, z_2A be integers such that z_RL ≤ z_2 and z_2 ≤ z_2A. Suppose there exist integers H and d such that 0 ≤ H, 0 ≤ d, 2 * (z_2A - z_RL) = recursive_line_hole_budget m n z z_RL - H - d, and (d = 0 → z_2A ≤ z_2). If recursive_line_hole_budget m n z z_RL ≤ 2, then z_2A = z_2.
-/

/-- Low-hole reduction ruling out overtake (Theorem 10). -/
theorem low_hole_reduction_ruling_out_overtake
    (m n : ℕ) (z z_RL z_2 z_2A : ℤ)
    (hle : z_RL ≤ z_2)
    (h_overtake : z_2 ≤ z_2A)
    (h_witness : ∃ (H d : ℤ), 0 ≤ H ∧ 0 ≤ d ∧
      2 * (z_2A - z_RL) = recursive_line_hole_budget m n z z_RL - H - d ∧
      (d = 0 → z_2A ≤ z_2))
    (h_low : recursive_line_hole_budget m n z z_RL ≤ 2) :
    z_2A = z_2 := by
  rcases h_witness with ⟨H, d, hH, hd, h_budget, h_limited⟩
  exact low_hole_reduction_overtake m n z z_RL z_2 z_2A H d
    hle h_overtake hH hd h_budget h_limited h_low
