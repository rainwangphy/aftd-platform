import AFTD.Prelude

/-!
# multiset_sum_finset

Topic: combinatorics   Node: f9cd37d7b2db

Provenance: helper lemma. step towards regular_sequence_additive_basis_cp_cnp

The set of all submultiset sums of a multiset S over an additive commutative group G, i.e. {sum T : T ≤ S} (equivalently the image of Multiset.sum on the powerset of S), as a finset.
-/

/-- The finset of all submultiset sums of S (the set Σ₀(S) = {σ(T) : T ≤ S}, including the empty sum 0). -/
noncomputable def multiset_sum_finset {G : Type*} [AddCommGroup G] [DecidableEq G] (S : Multiset G) : Finset G := (S.powerset.map Multiset.sum).toFinset
