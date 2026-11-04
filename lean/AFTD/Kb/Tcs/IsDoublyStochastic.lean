import AFTD.Prelude

/-!
# is_doubly_stochastic

Topic: graphs   Node: d4703f9b4d75

Provenance: formalization of a published result. Source: arXiv:2611.05048 Section 2; Birkhoff 1946

A real matrix Q on a finite set V is doubly stochastic if all entries are nonnegative and all row and column sums equal 1.
-/

/-- A matrix Q is doubly stochastic if its entries are nonnegative and every row and column sums to 1. -/
def is_doubly_stochastic {V : Type*} [Fintype V] (Q : V → V → ℝ) : Prop := (∀ i j, 0 ≤ Q i j) ∧ (∀ i, ∑ j, Q i j = 1) ∧ (∀ j, ∑ i, Q i j = 1)
