import AFTD.Prelude

/-!
# is_maximal_zero_sum_free

Topic: combinatorics   Node: abc79d4c5d8f

Provenance: formalization of a published result. Source: arXiv:2610.35819 Section 8

For a natural number n, an additive commutative group G, and a multiset S of elements of G, is_maximal_zero_sum_free n S asserts that S contains no submultiset of cardinality n with sum 0, and for every element x of G, the multiset S + {x} contains a submultiset of cardinality n with sum 0.
-/

/-- Predicate that a multiset over an additive commutative group G is maximal without n-term zero-sum submultisets. -/
def is_maximal_zero_sum_free (n : ℕ) {G : Type*} [AddCommGroup G] (S : Multiset G) : Prop := (¬ ∃ W : Multiset G, W ≤ S ∧ W.card = n ∧ W.sum = 0) ∧ (∀ x : G, ∃ W : Multiset G, W ≤ S + {x} ∧ W.card = n ∧ W.sum = 0)
