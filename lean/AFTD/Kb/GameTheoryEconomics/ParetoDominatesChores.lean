import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# pareto_dominates_chores

Topic: fair_division   Node: d9a7c628ecd0

An allocation of chores Pareto-dominates another if it costs every agent at most as much and some agent strictly less.
-/

/-- Pareto domination for chores (arXiv:2608.16130, Def. 2.4): under `τ` every agent has cost at most her cost under `σ`, and some agent has strictly smaller cost. -/
def pareto_dominates_chores {m n : ℕ} (c : Fin n → Fin m → ℝ) (τ σ : Fin m → Fin n) : Prop :=
  (∀ i, additive_valuation (c i) (bundle_of τ i) ≤ additive_valuation (c i) (bundle_of σ i)) ∧
    ∃ j, additive_valuation (c j) (bundle_of τ j) < additive_valuation (c j) (bundle_of σ j)
