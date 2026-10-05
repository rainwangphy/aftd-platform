import AFTD.Prelude

/-!
# gpa_cube

Topic: mechanism_design   Node: cb3eff78e474

The unit cube [0,1]^k.
-/

/-- The unit cube `[0,1]^k`. -/
def gpa_cube (k : ℕ) : Set (Fin k → ℝ) :=
  {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1}
