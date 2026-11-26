import AFTD.Prelude

/-!
# menu_principal_payoff

Topic: mechanism_design   Node: 81c6e3bcbc98

Provenance: formalization of a published result. Source: arXiv:2611.33095 Section 2.1

Given an item valuation x : E → ℝ, the principal's payoff from an agent action a : Option (Finset E) is ∑ i ∈ S, x i if a = some S and 0 if a = none.
-/

/-- The principal's realized payoff from an agent action (either abstaining or submitting an accepted set). -/
def menu_principal_payoff {E : Type*} (x : E → ℝ) (a : Option (Finset E)) : ℝ := match a with
  | none => 0
  | some S => ∑ i ∈ S, x i
