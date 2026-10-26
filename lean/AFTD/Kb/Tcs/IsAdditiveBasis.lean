import AFTD.Prelude

/-!
# IsAdditiveBasis

Topic: combinatorics   Node: de85a96f3224

Provenance: formalization of a published result. Source: scout/2610-13103-additive-bases-and-the-zero-sum-invariant-mathsf-n-g-for-gr.md:91

A multiset S over an additive commutative group G is an additive basis of G if for every element g of G, there exists a nonempty submultiset T of S (T ≤ S with T ≠ 0) whose multiset sum equals g.
-/

/-- A multiset S over G is an additive basis if every element of G is a sum of a nonempty submultiset of S. -/
def IsAdditiveBasis {G : Type*} [AddCommGroup G] (S : Multiset G) : Prop := ∀ g : G, ∃ T : Multiset G, T ≤ S ∧ T ≠ 0 ∧ T.sum = g
