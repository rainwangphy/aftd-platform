import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CostOfEf1
import AFTD.Kb.GameTheoryEconomics.CostOfEf1TwoLtOneSubInv

/-!
# not_forall_cost_of_ef1_ge_one_sub_inv

Topic: fair_division   Node: a82905d2383d

It is false that the cost of EF1 is at least 1 - 1/n for every n >= 1 (arXiv:2410.15738, Thm 7, fails at n = 2).
-/

/-- The lower bound `cost_of_ef1 n ≥ 1 - 1/n` of arXiv:2410.15738, Thm. 7, does not hold for all `n ≥ 1`. -/
theorem not_forall_cost_of_ef1_ge_one_sub_inv :
    ¬ ∀ n : ℕ, 1 ≤ n → 1 - 1 / (n : ℝ) ≤ cost_of_ef1 n := by
  intro h
  have := h 2 (by norm_num)
  have := cost_of_ef1_two_lt_one_sub_inv
  linarith
