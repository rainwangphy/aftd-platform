import AFTD.Prelude

/-!
# is_fractionally_pareto_optimal_two_type_chores

Topic: fair_division   Node: b4c64276084f

Provenance: formalization of a published result. Source: arXiv:2610.19099; folklore

For n agents indexed by Fin n, given agent-specific cost functions p, q : Fin n → ℝ and an integer allocation x, y : Fin n → ℕ of two chore types, (x, y) is fractionally Pareto optimal if there do not exist fractional assignments f, g : Fin n → ℝ with 0 ≤ f i and 0 ≤ g i for all i : Fin n, ∑ i, f i = ∑ i, (x i : ℝ), ∑ i, g i = ∑ i, (y i : ℝ), such that p i * f i + q i * g i ≤ p i * (x i : ℝ) + q i * (y i : ℝ) for all i : Fin n and p i * f i + q i * g i < p i * (x i : ℝ) + q i * (y i : ℝ) for some i : Fin n.
-/

/-- An allocation of two chore types is fractionally Pareto optimal if no feasible fractional allocation weakly decreases every agent's cost and strictly decreases at least one. -/
def is_fractionally_pareto_optimal_two_type_chores {n : ℕ} (p q : Fin n → ℝ) (x y : Fin n → ℕ) : Prop :=
  ¬ ∃ (f g : Fin n → ℝ),
    (∀ i, 0 ≤ f i) ∧
    (∀ i, 0 ≤ g i) ∧
    (∑ i, f i = ∑ i, (x i : ℝ)) ∧
    (∑ i, g i = ∑ i, (y i : ℝ)) ∧
    (∀ i, p i * f i + q i * g i ≤ p i * (x i : ℝ) + q i * (y i : ℝ)) ∧
    (∃ i, p i * f i + q i * g i < p i * (x i : ℝ) + q i * (y i : ℝ))
