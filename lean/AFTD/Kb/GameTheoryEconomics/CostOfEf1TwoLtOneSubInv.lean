import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CostOfEf1
import AFTD.Kb.GameTheoryEconomics.CostOfEf1TwoLe
import AFTD.Kb.GameTheoryEconomics.Ef1costAlphaLtHalf

/-!
# cost_of_ef1_two_lt_one_sub_inv

Topic: fair_division   Node: 04a50d9ca814

Provenance: erratum. Corrects: A Fair Allocation is Approximately Optimal for Indivisible Chores, or Is It?, arXiv:2410.15738 v1, Theorem 7 ('the cost of EF1 is at most 1 and at least 1 - 1/n'): false at n = 2, where the cost is at most 3 - 2 sqrt 2 < 1/2; the lower-bound construction needs EF1 among agents 1, 3, ..., n and so a third agent

The cost of EF1 for two agents is less than 1 - 1/2.
-/

/-- **Refutation of the lower bound in arXiv:2410.15738, Thm. 7, at `n = 2`.** Thm. 7 states "The cost of EF1 is at most 1 and at least 1 - 1/n"; for `n = 2` the cost of EF1 is `≤ 3 - 2√2 < 1/2 = 1 - 1/2`. -/
theorem cost_of_ef1_two_lt_one_sub_inv : cost_of_ef1 2 < 1 - 1 / (2 : ℕ) := by
  have := cost_of_ef1_two_le
  have h := ef1cost_alpha_lt_half
  push_cast
  linarith
