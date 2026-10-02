import AFTD.Prelude

/-!
# additive_valuation

Topic: fair_division   Node: d0f3fa53a4b3

The additive valuation with item values u: a bundle is worth the sum of its items' values.
-/

/-- The additive valuation with item values `u`. -/
def additive_valuation {m : ℕ} (u : Fin m → ℝ) : Finset (Fin m) → ℝ :=
  fun S => ∑ j ∈ S, u j
