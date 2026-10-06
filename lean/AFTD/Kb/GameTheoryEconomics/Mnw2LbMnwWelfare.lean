import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Mnw2LbVal
import AFTD.Kb.GameTheoryEconomics.Mnw2LbBundle
import AFTD.Kb.GameTheoryEconomics.IsMnwAllocation
import AFTD.Kb.GameTheoryEconomics.NashWelfare
import AFTD.Kb.GameTheoryEconomics.UtilitarianWelfare

/-!
# mnw2_lb_mnw_welfare

Topic: fair_division   Node: 9dd57ccf2317

Provenance: formalization of a published result. Source: The Price of Fairness for Indivisible Goods, arXiv:1905.04910, Theorem 5.4, lower-bound instance (m = 3, utilities (2/3, 1/3, 0) and (4/7 - eps, 1/7 + eps, 2/7), 0 < eps < 1/7)

For 0 < ε < 1/7, the allocation (0, 1, 1) is the unique MNW allocation of the three-good instance (all seven other allocations have strictly smaller Nash welfare), so every MNW allocation has social welfare 2/3 + (1/7 + ε + 2/7) = 23/21 + ε.
-/

/-- In the lower-bound instance every MNW allocation has utilitarian welfare 23/21 + ε. -/
theorem mnw2_lb_mnw_welfare (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1 / 7) (N : Fin 3 → Fin 2) (hN : is_mnw_allocation (mnw2_lb_val ε) N) : utilitarian_welfare (mnw2_lb_val ε) N = 23 / 21 + ε := by
  have hc := hN ![0, 1, 1]
  have h2 : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide
  simp only [nash_welfare, utilitarian_welfare, Fin.prod_univ_two, Fin.sum_univ_two, mnw2_lb_bundle] at hc ⊢
  rcases h2 (N 0) with a | a <;> rcases h2 (N 1) with b | b <;> rcases h2 (N 2) with c | c <;>
    simp [a, b, c, mnw2_lb_val] at hc ⊢ <;> nlinarith
