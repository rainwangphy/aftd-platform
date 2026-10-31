import AFTD.Prelude

/-!
# AffineForm

Topic: algebraic_complexity   Node: 0ee244b8f97e

Provenance: formalization of a published result. Source: arXiv:2610.37677, Section 1.1

An affine linear form parameterized by a type F and an arity m : ℕ consists of a constant term c0 : F and a tuple of linear coefficients c : Fin m → F.
-/

/-- An affine linear form parameterized by type F and arity m. -/
structure AffineForm (F : Type*) (m : ℕ) where
  c0 : F
  c : Fin m → F
