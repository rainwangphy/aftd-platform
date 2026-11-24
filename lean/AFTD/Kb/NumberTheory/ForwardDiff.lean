import AFTD.Prelude

/-!
# forward_diff

Topic: elementary_number_theory   Node: 4b1df9f98bf9

Provenance: formalization of a published result. Source: arXiv:2611.26953, Section 1.1

The forward difference of a function f from the natural numbers to the integers is given by (Δ f)(x) = f(x + 1) - f(x).
-/

/-- Forward difference of an integer-valued function on the natural numbers. -/
def forward_diff (f : ℕ → ℤ) : ℕ → ℤ := fun x => f (x + 1) - f x
