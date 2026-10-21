import AFTD.Prelude

/-!
# degreeSpace

Topic: circuits   Node: 1cb6ddf39fb1

Provenance: formalization of a published result. Source: arXiv:2610.19174, Section 2 and Listing A.1

For a commutative ring K, a finite type ι with decidable equality, and a natural number d, degreeSpace K ι d is the K-submodule of (ι → Bool) → K spanned by the set of functions f : (ι → Bool) → K for which there exists a finite subset S : Finset ι with S.card ≤ d such that f x = ∏ i ∈ S, if x i then (1 : K) else 0.
-/

/-- The submodule of functions on the Boolean cube represented by multilinear polynomials of degree at most d. -/
def degreeSpace (K : Type*) [CommRing K] (ι : Type*) [Fintype ι] [DecidableEq ι] (d : ℕ) :
    Submodule K ((ι → Bool) → K) := Submodule.span K { f | ∃ (S : Finset ι), S.card ≤ d ∧ f = fun x => ∏ i ∈ S, if x i then (1 : K) else 0 }
