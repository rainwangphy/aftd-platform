import AFTD.Prelude

/-!
# pyranim_is_order_ideal

Topic: combinatorial_games   Node: f15af4ea24e7

Provenance: formalization of a published result. Source: arXiv:2611.16153 Def. 1.1

A finite set of chips X : Finset (ℕ × ℕ) is an order ideal if whenever p ∈ X and a, b are natural numbers with p.1 ≤ a ≤ b ≤ p.2, the subinterval chip (a, b) also belongs to X.
-/

/-- Predicate asserting that a set of Pyranim chips is an order ideal under interval containment. -/
def pyranim_is_order_ideal (X : Finset (ℕ × ℕ)) : Prop := ∀ p ∈ X, ∀ a ∈ Finset.Icc p.1 p.2, ∀ b ∈ Finset.Icc a p.2, (a, b) ∈ X
