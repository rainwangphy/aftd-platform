import AFTD.Prelude

/-!
# is_scaled_bivalued_chores

Topic: fair_division   Node: 14eb87816b53

Provenance: formalization of a published result. Source: arXiv:2610.19099

Given ratio r : ℝ and a chore cost profile c : Fin n → Fin m → ℝ over n agents and m chores, c is scaled bivalued with ratio r if there exists a vector of positive scales a : Fin n → ℝ such that for every agent i : Fin n and chore g : Fin m, c i g = a i or c i g = r * a i.
-/

/-- A chore cost profile c : Fin n → Fin m → ℝ is scaled bivalued with ratio r if every cost c i g is a_i or r * a_i for some positive a_i. -/
def is_scaled_bivalued_chores {m n : ℕ} (r : ℝ) (c : Fin n → Fin m → ℝ) : Prop := ∃ a : Fin n → ℝ, (∀ i, 0 < a i) ∧ ∀ i g, c i g = a i ∨ c i g = r * a i
