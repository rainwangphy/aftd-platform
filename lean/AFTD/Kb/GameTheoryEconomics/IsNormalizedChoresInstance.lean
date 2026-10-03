import AFTD.Prelude

/-!
# is_normalized_chores_instance

Topic: fair_division   Node: c11bd7c1b8df

A chores instance is normalized if all costs are nonnegative and every agent's total cost is 1.
-/

/-- A chores instance in the model of arXiv:2410.15738 (Sec. 2): every cost is nonnegative and every agent's costs are normalised, `c i (O) = 1`. -/
def is_normalized_chores_instance {m n : ℕ} (c : Fin n → Fin m → ℝ) : Prop :=
  (∀ i j, 0 ≤ c i j) ∧ ∀ i, ∑ j, c i j = 1
