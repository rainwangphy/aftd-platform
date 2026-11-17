import AFTD.Prelude
import AFTD.Kb.Tcs.FactorizationMobiusToTop
import AFTD.Kb.Tcs.IsNatFactorization
import AFTD.Kb.Tcs.IsFactorizationCoarsening

/-!
# factorizationMobiusToTop_two_three

Topic: combinatorics   Node: 88e9fb6fcf6e

Provenance: helper lemma. arXiv:2611.18194 (The Möbius function of factorizations with a simple prime factor): sanity lemma for the factorization-poset definitions

In the factorization poset of 6, the Möbius function between the factorization 2·3 and 6 is -1.
-/

theorem factorizationMobiusToTop_two_three : factorizationMobiusToTop 6 {2, 3} = -1 := by
  have hset : ∀ y : Multiset ℕ,
      (IsNatFactorization 6 y ∧ IsFactorizationCoarsening {2, 3} y ∧
        Multiset.card y < Multiset.card ({2, 3} : Multiset ℕ)) ↔ y = {6} := by
    intro y
    constructor
    · rintro ⟨⟨_, h2⟩, _, h3⟩
      have hc : Multiset.card y = 0 ∨ Multiset.card y = 1 := by simp at h3; omega
      rcases hc with hc | hc
      · rw [Multiset.card_eq_zero.mp hc] at h2; simp at h2
      · obtain ⟨a, rfl⟩ := Multiset.card_eq_one.mp hc
        simp at h2; simp [h2]
    · rintro rfl
      refine ⟨⟨by simp, by simp⟩, ⟨{{2, 3}}, by simp, by simp, by simp⟩, by simp⟩
  rw [factorizationMobiusToTop]
  have hfs : (∑ᶠ (y : Multiset ℕ) (_ : IsNatFactorization 6 y ∧ IsFactorizationCoarsening {2, 3} y ∧
        Multiset.card y < Multiset.card ({2, 3} : Multiset ℕ)), factorizationMobiusToTop 6 y) =
      factorizationMobiusToTop 6 {6} := by
    simp_rw [hset]
    rw [finsum_eq_single _ ({6} : Multiset ℕ)]
    · simp
    · intro y hy; simp [hy]
  rw [hfs, factorizationMobiusToTop]
  simp
