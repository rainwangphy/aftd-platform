import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GoodsUtility

/-!
# pareto_dominates_goods

Topic: fair_division   Node: 5267c7013ea7

Allocation tau Pareto-dominates sigma: every agent weakly prefers tau and some agent strictly prefers it.
-/

/-- Pareto domination for goods: under `τ` every agent is at least as well off as under `σ`, and some agent strictly better off. -/
def pareto_dominates_goods {m n : ℕ} (u : Fin n → Fin m → ℝ) (τ σ : Fin m → Fin n) : Prop :=
  (∀ i, goods_utility u σ i ≤ goods_utility u τ i) ∧ ∃ i, goods_utility u σ i < goods_utility u τ i
