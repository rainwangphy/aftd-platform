import AFTD.Prelude
import AFTD.Kb.NumberTheory.RecurrenceBMap
import AFTD.Kb.NumberTheory.RecurrenceBInv

/-!
# recurrence_b_map_bijective

Topic: elementary_number_theory   Node: 679fce429337

Provenance: helper lemma. arXiv:2610.34300 Proposition 7

For any integer k ≥ 2, the transition map of recurrence (B) on (ℤ/3ℤ)^k is bijective.
-/

theorem recurrence_b_map_bijective_left_inv (k : ℕ) (hk : 2 ≤ k) :
    Function.LeftInverse (recurrence_b_inv k hk) (recurrence_b_map k) := by
  intro w
  ext ⟨i, hi⟩
  dsimp [recurrence_b_inv, recurrence_b_map]
  by_cases h0 : i = 0
  · rw [if_pos h0]
    have h1 : ¬ (k - 1 + 1 < k) := by omega
    have h2 : k - 2 + 1 < k := by omega
    rw [dif_neg h1, dif_pos h2]
    subst h0
    have heq : (⟨k - 2 + 1, h2⟩ : Fin k) = ⟨k - 1, by omega⟩ := by
      apply Fin.ext
      dsimp
      omega
    rw [heq, add_sub_cancel_right]
  · rw [if_neg h0]
    have h1 : i - 1 + 1 < k := by omega
    rw [dif_pos h1]
    have heq : (⟨i - 1 + 1, h1⟩ : Fin k) = ⟨i, hi⟩ := by
      apply Fin.ext
      dsimp
      omega
    rw [heq]

/-- Bijectivity of the transition map of recurrence B for k ≥ 2. -/
theorem recurrence_b_map_bijective (k : ℕ) (hk : 2 ≤ k) : Function.Bijective (recurrence_b_map k) := by
  have hlinv := recurrence_b_map_bijective_left_inv k hk
  have hinj : Function.Injective (recurrence_b_map k) := hlinv.injective
  exact Finite.injective_iff_bijective.mp hinj
