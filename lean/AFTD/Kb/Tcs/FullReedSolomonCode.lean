import AFTD.Prelude

/-!
# full_reed_solomon_code

Topic: information   Node: b2cda4a9099f

Provenance: formalization of a published result. Source: arXiv:2611.07607

The full-length Reed-Solomon code of dimension $k$ over a commutative ring $F$ is the set of functions from $F$ to $F$ obtained by evaluating polynomials of degree strictly less than $k$.
-/

/-- The full-length Reed-Solomon code of dimension k over F consists of all evaluations of polynomials of degree less than k. -/
def full_reed_solomon_code (F : Type*) [CommRing F] (k : ℕ) : Set (F → F) := {c | ∃ P : Polynomial F, Polynomial.degree P < (k : WithBot ℕ) ∧ c = fun α => Polynomial.eval α P}
