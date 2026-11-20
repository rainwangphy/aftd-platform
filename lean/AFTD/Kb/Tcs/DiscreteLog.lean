import AFTD.Prelude

/-!
# discrete_log

Topic: combinatorics   Node: f07e2160ed01

Provenance: formalization of a published result. Source: arXiv:2611.22205 Section 3

For an element x and base g in a monoid M, discrete_log g x is the minimal natural number m such that g ^ m = x, or 0 if no such m exists.
-/

/-- Discrete logarithm of an element x with respect to base g in a monoid M. -/
noncomputable def discrete_log {M : Type*} [Monoid M] (g x : M) : ℕ := by classical exact if h : ∃ m : ℕ, g ^ m = x then Nat.find h else 0
