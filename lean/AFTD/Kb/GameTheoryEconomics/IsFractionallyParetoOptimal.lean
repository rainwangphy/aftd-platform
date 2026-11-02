import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GoodsUtility

/-!
# is_fractionally_pareto_optimal

Topic: fair_division   Node: e0600e6ad625

Provenance: formalization of a published result. Source: arXiv:2610.14994, Section 2

An allocation of goods σ is fractionally Pareto optimal for additive valuations u if no fractional assignment x weakly improves every agent's additive utility and strictly improves at least one agent's additive utility.
-/

/-- Fractional Pareto optimality for additive goods: no fractional assignment weakly improves all agents and strictly improves at least one. -/
def is_fractionally_pareto_optimal {m n : ℕ} (u : Fin n → Fin m → ℝ) (σ : Fin m → Fin n) : Prop := ¬ ∃ x : Fin n → Fin m → ℝ,
    (∀ i g, 0 ≤ x i g) ∧
    (∀ g, ∑ i, x i g = 1) ∧
    (∀ i, goods_utility u σ i ≤ ∑ g, u i g * x i g) ∧
    (∃ i, goods_utility u σ i < ∑ g, u i g * x i g)
