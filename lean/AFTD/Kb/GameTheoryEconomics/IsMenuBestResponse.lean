import AFTD.Prelude

/-!
# is_menu_best_response

Topic: mechanism_design   Node: 3d8f49412159

Provenance: formalization of a published result. Source: arXiv:2611.33095 Section 2.1

Given a set of finite sets A : Set (Finset E), an agent valuation y : E → ℝ, and an action a : Option (Finset E), is_menu_best_response A y a holds if a is available (either a = none or a = some S with S ∈ A) and the agent utility (0 for none and ∑ i ∈ S, y i for some S) is at least 0 and weakly dominates ∑ i ∈ S, y i for every S ∈ A.
-/

/-- An action is a best response for the agent if it is available (accepted or abstention) and maximizes agent utility. -/
def is_menu_best_response {E : Type*} (A : Set (Finset E)) (y : E → ℝ) (a : Option (Finset E)) : Prop := (match a with | none => True | some S => S ∈ A) ∧
  (∀ S ∈ A, (∑ i ∈ S, y i) ≤ (match a with | none => 0 | some T => ∑ i ∈ T, y i)) ∧
  (0 ≤ match a with | none => 0 | some T => ∑ i ∈ T, y i)
