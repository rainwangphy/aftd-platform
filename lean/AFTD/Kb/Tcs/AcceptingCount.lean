import AFTD.Prelude

/-!
# acceptingCount

Topic: circuits   Node: 6965e58b7bf5

Provenance: formalization of a published result. Source: arXiv:2610.19174, Section 2.3 and Listing A.13

The number of accepting inputs |f⁻¹(1)| of a Boolean function f.
-/

/-- The number of accepting inputs of a Boolean function. -/
def acceptingCount {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ := Fintype.card {x : Fin n → Bool // f x = true}
