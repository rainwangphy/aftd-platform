import AFTD.Prelude

/-!
# IsNatFactorization

Topic: combinatorics   Node: 4334d00d089e

Provenance: formalization of a published result. Source: arXiv:2611.18194 (The Möbius function of factorizations with a simple prime factor), Section 1 (factorizations of n)

A factorization of a natural number n is a multiset of integers greater than 1 whose product is n.
-/

/-- `x` is a factorization of `n`: a multiset of integers greater than one whose product is `n` (order ignored). -/
def IsNatFactorization (n : ℕ) (x : Multiset ℕ) : Prop :=
  (∀ a ∈ x, 1 < a) ∧ x.prod = n
