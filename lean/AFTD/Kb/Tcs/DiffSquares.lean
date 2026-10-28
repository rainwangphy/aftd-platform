import AFTD.Prelude

/-!
# diff_squares

Topic: combinatorics   Node: 884ab06d4197

Provenance: formalization of a published result. Source: arXiv:2610.34758, Section 1

The set of squared differences of a finite subset $A$ in a commutative ring is $(A - A)^2 = \{(a - b)^2 : a, b \in A\}$.
-/

/-- The set of squared differences of a finite subset in a commutative ring. -/
def diff_squares {F : Type*} [CommRing F] [DecidableEq F] (A : Finset F) : Finset F := (A ×ˢ A).image (fun (a, b) => (a - b) ^ 2)
