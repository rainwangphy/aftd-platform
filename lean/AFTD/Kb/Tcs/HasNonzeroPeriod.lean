import AFTD.Prelude

/-!
# has_nonzero_period

Topic: cryptography   Node: 0c9a9b247685

Provenance: formalization of a published result. Source: arXiv:2610.32239 Section 2

A Boolean function f has a nonzero period if there exists a nonzero vector a such that f(x + a) = f(x) for all x.
-/

/-- A Boolean function has a nonzero period if it is invariant under translation by some nonzero vector. -/
def has_nonzero_period {n : ℕ} (f : (Fin n → ZMod 2) → ZMod 2) : Prop := ∃ a : Fin n → ZMod 2, a ≠ 0 ∧ ∀ x, f (x + a) = f x
