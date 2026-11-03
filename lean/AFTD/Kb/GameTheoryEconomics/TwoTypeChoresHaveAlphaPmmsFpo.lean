import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsTwoTypeAllocation
import AFTD.Kb.GameTheoryEconomics.IsFractionallyParetoOptimalTwoTypeChores
import AFTD.Kb.GameTheoryEconomics.IsAlphaPmmsTwoTypeChores

/-!
# two_type_chores_have_alpha_pmms_fpo

Topic: fair_division   Node: 5cca4aa93185

Provenance: formalization of a published result. Source: OP-886; arXiv:2610.19099

The property that for any number of agents n ≥ 2, non-negative chore totals a, b : ℕ, and agent-specific strictly positive chore cost functions p, q : Fin n → ℝ, there exists an integer count allocation x, y : Fin n → ℕ satisfying is_two_type_allocation n a b x y that is fractionally Pareto optimal and alpha-PMMS fair.
-/

/-- Universal existence of an alpha-PMMS fractionally Pareto optimal allocation for two chore types. -/
def two_type_chores_have_alpha_pmms_fpo (α : ℝ) : Prop :=
  ∀ (n : ℕ) (_ : 2 ≤ n) (a b : ℕ) (p q : Fin n → ℝ)
    (_ : ∀ i, 0 < p i) (_ : ∀ i, 0 < q i),
    ∃ (x y : Fin n → ℕ),
      is_two_type_allocation n a b x y ∧
      is_fractionally_pareto_optimal_two_type_chores p q x y ∧
      is_alpha_pmms_two_type_chores α p q x y
