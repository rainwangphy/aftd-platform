import AFTD.Prelude

/-!
# has_binary_marginals

Topic: fair_division   Node: 5547e2b6d10d

Every marginal value of the set function is 0 or 1.
-/

/-- Every marginal value is 0 or 1. -/
def has_binary_marginals {m : ℕ} (v : Finset (Fin m) → ℝ) : Prop :=
  ∀ S j, j ∉ S → v (insert j S) = v S ∨ v (insert j S) = v S + 1
