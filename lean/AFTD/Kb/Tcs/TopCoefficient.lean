import AFTD.Prelude

/-!
# topCoefficient

Topic: circuits   Node: 819fe3919591

Provenance: formalization of a published result. Source: arXiv:2610.19174, Section 2.3 eq (3) and Listing A.13

For an implicit natural number n and a Boolean-valued function f : (Fin n → Bool) → Bool, topCoefficient f is the integer defined by the sum over all x : Fin n → Bool of: if f x is true then ∏ i : Fin n, (if x i then (1 : ℤ) else -1), else 0.
-/

/-- The full-cube multilinear coefficient c_f of a Boolean function f. -/
def topCoefficient {n : ℕ} (f : (Fin n → Bool) → Bool) : ℤ := ∑ x : Fin n → Bool, (if f x then (∏ i : Fin n, (if x i then (1 : ℤ) else -1)) else 0)
