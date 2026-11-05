import AFTD.Prelude

/-!
# exists_pair_same_fst_of_card_gt

Topic: combinatorics   Node: 6dd064917762

Provenance: helper lemma. arXiv:2611.03878 Theorem 3.1

Every finite subset S of Fin m × Fin k with cardinality strictly greater than m contains two distinct elements sharing the same first coordinate.
-/

/-- By pigeonhole on the first coordinate, any subset of Fin m × Fin k of size > m has two distinct elements with equal first coordinate. -/
theorem exists_pair_same_fst_of_card_gt {m k : ℕ} {S : Finset (Fin m × Fin k)} (hS : m < S.card) :
  ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ u.1 = v.1 := by
  have h_le : (S.image Prod.fst).card ≤ m := by
    calc (S.image Prod.fst).card ≤ Fintype.card (Fin m) := Finset.card_le_univ _
    _ = m := Fintype.card_fin m
  have h_lt : (S.image Prod.fst).card < S.card := lt_of_le_of_lt h_le hS
  exact Finset.exists_ne_map_eq_of_card_image_lt h_lt
