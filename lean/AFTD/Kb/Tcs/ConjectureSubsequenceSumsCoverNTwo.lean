import AFTD.Prelude

/-!
# conjecture_subsequence_sums_cover_n_two

Topic: combinatorics   Node: 98e8e701084c

Provenance: formalization of a published result. Source: arXiv:2610.35819 Corollary 8.3

For n = 2 and any rank r ≥ 1, every sequence of length 2^r over (ZMod 2)^r containing no 2-term zero-sum has the property that its 2-term subsequence sums cover all 2^r - 1 nonzero elements.
-/

/-- Corollary 8.3: Conjecture 8.1 holds for n = 2 in any rank r ≥ 1. -/
theorem conjecture_subsequence_sums_cover_n_two
    (r : ℕ) (hr : 1 ≤ r) (S : Multiset (Fin r → ZMod 2))
    (hS_card : S.card = 2^r)
    (hS_zs : 0 ∉ ((S.powersetCard 2).map Multiset.sum).toFinset) :
    ((S.powersetCard 2).map Multiset.sum).toFinset = Finset.univ \ {0} := by
  have _ := hr
  have hS_nodup : S.Nodup := by
    rw [Multiset.nodup_iff_le]
    intro a hle
    apply hS_zs
    rw [Multiset.mem_toFinset, Multiset.mem_map]
    refine ⟨a ::ₘ a ::ₘ 0, ?_, ?_⟩
    · rw [Multiset.mem_powersetCard]
      exact ⟨hle, rfl⟩
    · ext i
      simp [CharTwo.add_self_eq_zero]
  have hS_all : ∀ x : Fin r → ZMod 2, x ∈ S := by
    have hu : S.toFinset = Finset.univ := by
      rw [← Finset.card_eq_iff_eq_univ]
      rw [Multiset.toFinset_card_of_nodup hS_nodup]
      rw [hS_card]
      simp
    intro x
    rw [← Multiset.mem_toFinset, hu]
    exact Finset.mem_univ x
  ext g
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and]
  constructor
  · intro hg
    rintro rfl
    exact hS_zs hg
  · intro hg
    rw [Multiset.mem_toFinset, Multiset.mem_map]
    refine ⟨0 ::ₘ g ::ₘ 0, ?_, ?_⟩
    · rw [Multiset.mem_powersetCard]
      refine ⟨?_, rfl⟩
      have h_not : (0 : Fin r → ZMod 2) ∉ (g ::ₘ 0 : Multiset (Fin r → ZMod 2)) := by
        simp [Ne.symm hg]
      rw [Multiset.cons_le_of_notMem h_not]
      exact ⟨hS_all 0, Multiset.singleton_le.mpr (hS_all g)⟩
    · simp
