import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Pmms3cCostNat
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.Pmms3cCost

/-!
# pmms3c_cost_nat_eq

Topic: fair_division   Node: bbe97e401ad1

The fold computing agent i's cost of the chores selected by P agrees with the additive cost of that set.
-/

theorem pmms3c_cost_nat_eq (i : Fin 3) (P : Fin 9 → Bool) : ((pmms3c_cost_nat i P : ℕ) : ℝ) = additive_valuation (fun g => (pmms3c_cost i g : ℝ)) (Finset.univ.filter fun g => P g = true) := by
  unfold additive_valuation pmms3c_cost_nat
  rw [Finset.sum_filter]
  simp [Fin.sum_univ_succ, List.finRange_succ]
