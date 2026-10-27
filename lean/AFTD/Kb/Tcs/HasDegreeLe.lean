import AFTD.Prelude

/-!
# has_degree_le

Topic: cryptography   Node: f182be1263c9

Provenance: formalization of a published result. Source: arXiv:2610.32239 Section 2

A Boolean function f has algebraic degree at most d if it can be represented as a sum of monomials of degree at most d over ZMod 2.
-/

/-- A Boolean function has algebraic degree at most d if its algebraic normal form contains only monomials of degree at most d. -/
def has_degree_le {n : ℕ} (f : (Fin n → ZMod 2) → ZMod 2) (d : ℕ) : Prop := ∃ c : Finset (Finset (Fin n)), (∀ S ∈ c, S.card ≤ d) ∧ ∀ x, f x = ∑ S ∈ c, ∏ i ∈ S, x i
