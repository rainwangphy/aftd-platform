import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Mnw2LbVal
import AFTD.Kb.GameTheoryEconomics.Mnw2LbBundle
import AFTD.Kb.GameTheoryEconomics.UtilitarianWelfare

/-!
# mnw2_lb_opt_welfare

Topic: fair_division   Node: f6d191c656eb

Provenance: formalization of a published result. Source: The Price of Fairness for Indivisible Goods, arXiv:1905.04910, Theorem 5.4, lower-bound instance (m = 3, utilities (2/3, 1/3, 0) and (4/7 - eps, 1/7 + eps, 2/7), 0 < eps < 1/7)

Giving goods 0 and 1 to agent 0 and good 2 to agent 1 yields social welfare 2/3 + 1/3 + 2/7 = 9/7.
-/

/-- In the lower-bound instance the allocation (0, 0, 1) has utilitarian welfare 9/7. -/
theorem mnw2_lb_opt_welfare (ε : ℝ) : utilitarian_welfare (mnw2_lb_val ε) ![0, 0, 1] = 9 / 7 := by
  simp only [utilitarian_welfare, Fin.sum_univ_two, mnw2_lb_bundle]
  have a0 : (![0, 0, 1] : Fin 3 → Fin 2) 0 = 0 := rfl
  have a1 : (![0, 0, 1] : Fin 3 → Fin 2) 1 = 0 := rfl
  have a2 : (![0, 0, 1] : Fin 3 → Fin 2) 2 = 1 := rfl
  simp [mnw2_lb_val, a0, a1, a2] <;> norm_num
