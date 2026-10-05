import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Mnw2LbVal
import AFTD.Kb.GameTheoryEconomics.Mnw2LbBundle
import AFTD.Kb.GameTheoryEconomics.IsMnwAllocation
import AFTD.Kb.GameTheoryEconomics.NashWelfare

/-!
# mnw2_lb_is_mnw

Topic: fair_division   Node: 9530834418d8

For 0 < ε < 1/7, the allocation N = (0, 1, 1) (good 0 to agent 0, goods 1 and 2 to agent 1) has Nash welfare (2/3)(3/7 + ε), the largest among all eight allocations, so it is an MNW allocation.
-/

/-- In the lower-bound instance, giving good 0 to agent 0 and goods 1, 2 to agent 1 maximizes Nash welfare. -/
theorem mnw2_lb_is_mnw (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1 / 7) : is_mnw_allocation (mnw2_lb_val ε) ![0, 1, 1] := by
  intro τ
  have h2 : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide
  simp only [nash_welfare, Fin.prod_univ_two, mnw2_lb_bundle]
  rcases h2 (τ 0) with a | a <;> rcases h2 (τ 1) with b | b <;> rcases h2 (τ 2) with c | c <;>
    simp [a, b, c, mnw2_lb_val] <;> nlinarith
