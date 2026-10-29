import AFTD.Prelude

/-!
# subsequence_sums

Topic: combinatorics   Node: c26d22670a5f

Provenance: formalization of a published result. Source: arXiv:2610.35819 Section 8

For a natural number n and a multiset S of elements of an additive commutative monoid G with decidable equality, subsequence_sums n S is the finite set (Finset G) of all elements of G that can be written as the sum of a submultiset of S of cardinality n.
-/

/-- The finite set of sums of all length-n submultisets of a multiset S. -/
def subsequence_sums (n : ℕ) {G : Type*} [AddCommMonoid G] [DecidableEq G] (S : Multiset G) : Finset G := ((S.powerset.filter (fun U => U.card = n)).map Multiset.sum).toFinset
