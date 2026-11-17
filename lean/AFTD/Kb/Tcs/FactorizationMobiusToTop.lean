import AFTD.Prelude
import AFTD.Kb.Tcs.IsNatFactorization
import AFTD.Kb.Tcs.IsFactorizationCoarsening

/-!
# factorizationMobiusToTop

Topic: combinatorics   Node: 0a11d2e2b738

Provenance: formalization of a published result. Source: arXiv:2611.18194 (The Möbius function of factorizations with a simple prime factor), Section 1 and the recursion used in the proof of Theorem 6

For a natural number n and a multiset x of natural numbers, factorizationMobiusToTop n x (n first, then x) is the integer defined by recursion on the number of elements of x: it is 1 if x has at most one element; otherwise it is minus the sum, over all multisets y that are factorizations of n (every element greater than 1, product n), are coarsenings of x (IsFactorizationCoarsening x y) and have fewer elements than x, of factorizationMobiusToTop n y. When x is a factorization of n this is the Möbius function μ(x, n) of the poset of factorizations of n ordered by refinement, between x and the top element: the top element is the factorization with at most one factor, and the factorizations strictly above x are exactly its coarsenings with fewer factors. Values at multisets x that are not factorizations of n carry no meaning.
-/

/-- The Möbius function `μ(x, n)` of the poset of factorizations of `n` ordered by refinement, between a factorization `x` and the top element `n`, by its defining recursion: `μ(x, n) = 1` when `x` is the top element and `μ(x, n) = -∑_{x < y ≤ n} μ(y, n)` otherwise. For a factorization `x` of `n`, `x` is the top element exactly when it has at most one factor (`{n}`, or the empty factorization when `n = 1`), and the factorizations strictly above `x` are its coarsenings with fewer factors (a coarsening with as many factors as `x` is `x` itself). -/
noncomputable def factorizationMobiusToTop (n : ℕ) (x : Multiset ℕ) : ℤ :=
  if x.card ≤ 1 then 1
  else -∑ᶠ (y : Multiset ℕ)
      (_ : IsNatFactorization n y ∧ IsFactorizationCoarsening x y ∧ y.card < x.card),
      factorizationMobiusToTop n y
termination_by x.card
