import AFTD.Prelude

/-!
# exists_pair_same_snd_of_card_gt

Topic: combinatorics   Node: 920f5491dfd9

Provenance: helper lemma. arXiv:2611.03878 Theorem 3.1

Every finite subset S of Fin m × Fin k with cardinality strictly greater than k contains two distinct elements sharing the same second coordinate.
-/

/-- By pigeonhole on the second coordinate, any subset of Fin m × Fin k of size > k has two distinct elements with equal second coordinate. -/
theorem exists_pair_same_snd_of_card_gt {m k : ℕ} {S : Finset (Fin m × Fin k)} (hS : k < S.card) :
  ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ u.2 = v.2 := by
  by_contra! h
  have h_inj : Set.InjOn Prod.snd (S : Set (Fin m × Fin k)) := by
    intro u hu v hv heq
    by_contra hne
    exact h u hu v hv hne heq
  have h_maps : Set.MapsTo Prod.snd (S : Set (Fin m × Fin k)) (Finset.univ : Finset (Fin k)) := by
    intro x _
    exact Finset.mem_univ _
  have h_le := Finset.card_le_card_of_injOn Prod.snd h_maps h_inj
  simp only [Finset.card_univ, Fintype.card_fin] at h_le
  exact Nat.not_le_of_lt hS h_le
