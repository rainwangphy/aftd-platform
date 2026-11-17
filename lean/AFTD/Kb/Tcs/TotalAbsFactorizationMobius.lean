import AFTD.Prelude
import AFTD.Kb.Tcs.IsNatFactorization
import AFTD.Kb.Tcs.FactorizationMobiusToTop

/-!
# totalAbsFactorizationMobius

Topic: combinatorics   Node: 29a39b7233c8

Provenance: formalization of a published result. Source: arXiv:2611.18194 (The Möbius function of factorizations with a simple prime factor), Section 3 (a(n), OEIS A369713)

For a natural number n, totalAbsFactorizationMobius n is the natural number a(n) = Σ_x |factorizationMobiusToTop n x|: the sum, over all factorizations x of n (multisets of integers greater than 1 with product n, of which there are finitely many), of the absolute value, taken as a natural number (Int.natAbs), of the factorization-poset Möbius function μ(x, n) = factorizationMobiusToTop n x.
-/

/-- The total absolute Möbius function `a(n) = ∑_x |μ(x, n)|`, summed over all factorizations `x` of `n` (OEIS A369713). The set of factorizations of `n` is finite, so the `finsum` is a finite sum. -/
noncomputable def totalAbsFactorizationMobius (n : ℕ) : ℕ :=
  ∑ᶠ (x : Multiset ℕ) (_ : IsNatFactorization n x), (factorizationMobiusToTop n x).natAbs
