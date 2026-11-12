import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsBudgetFeasible
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# is_budget_feasible_empty

Topic: fair_division   Node: 2bce24116880

Provenance: helper lemma. arXiv:2611.12740 Section 2

The empty allocation giving no items to any agent is budget-feasible whenever all agent budgets are nonnegative.
-/

/-- The empty allocation is budget-feasible whenever budgets are nonnegative. -/
theorem is_budget_feasible_empty {m n : ℕ} (s : Fin m → ℝ) (B : Fin n → ℝ)
    (hB : ∀ i, 0 ≤ B i) :
    is_budget_feasible s B (fun _ => ∅) := by
  unfold is_budget_feasible
  constructor
  · intro i j _ _; simp
  · intro i
    unfold additive_valuation
    simp only [Finset.sum_empty]
    exact hB i
