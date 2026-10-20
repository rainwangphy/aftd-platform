import AFTD.Prelude

/-!
# WeightedSetPackingInstance

Topic: approximation   Node: d195782465ef

Provenance: formalization of a published result. Source: arXiv:2610.10036 Sec. 3

For a type α with decidable equality and k : ℕ, an instance of Maximum Weighted k-Set Packing WeightedSetPackingInstance α k consists of a finite set family : Finset (Finset α) of nonempty finite subsets of α of cardinality at most k, and a weight function weight : Finset α → ℚ assigning strictly positive rational weight to every set in family.
-/

/-- An instance of Maximum Weighted k-Set Packing over a universe α. -/
structure WeightedSetPackingInstance (α : Type*) [DecidableEq α] (k : ℕ) where
  family : Finset (Finset α)
  card_le : ∀ s ∈ family, s.card ≤ k
  nonempty : ∀ s ∈ family, s.Nonempty
  weight : Finset α → ℚ
  weight_pos : ∀ s ∈ family, 0 < weight s
