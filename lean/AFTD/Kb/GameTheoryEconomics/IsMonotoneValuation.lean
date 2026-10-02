import AFTD.Prelude

/-!
# is_monotone_valuation

Topic: fair_division   Node: f335a58ffb84

A valuation is monotone and nonnegative: v(∅) ≥ 0 and S ⊆ T implies v(S) ≤ v(T).
-/

/-- A monotone valuation into the nonnegative reals: `0 ≤ v ∅` and `S ⊆ T → v S ≤ v T`. -/
def is_monotone_valuation {m : ℕ} (v : Finset (Fin m) → ℝ) : Prop :=
  0 ≤ v ∅ ∧ ∀ S T, S ⊆ T → v S ≤ v T
