import AFTD.Prelude

/-!
# is_submodular

Topic: fair_division   Node: 7bdb654525f4

A set function is submodular: for S inside T and j outside T, the marginal value of j over T is at most its marginal value over S.
-/

/-- A set function is submodular: marginal values shrink as the set grows. -/
def is_submodular {m : ℕ} (v : Finset (Fin m) → ℝ) : Prop :=
  ∀ S T j, S ⊆ T → j ∉ T → v (insert j T) - v T ≤ v (insert j S) - v S
