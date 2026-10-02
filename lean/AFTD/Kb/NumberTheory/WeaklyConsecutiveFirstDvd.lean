import AFTD.Prelude
import AFTD.Kb.NumberTheory.IsWeaklyConsecutive
import AFTD.Kb.NumberTheory.DvdOfDivCeilLe
import AFTD.Kb.NumberTheory.FinCardFilterDvd
import AFTD.Kb.NumberTheory.PermCardFilterDvdSucc

/-!
# weakly_consecutive_first_dvd

Topic: elementary_number_theory   Node: 9861d624fcb7

In a weakly consecutive sequence of length k, the first term divides k.
-/

theorem weakly_consecutive_first_dvd {k : ℕ} (σ : Equiv.Perm (Fin k))
    (hσ : is_weakly_consecutive σ) (hk : 0 < k) : (σ ⟨0, hk⟩ : ℕ) + 1 ∣ k := by
  set m := (σ ⟨0, hk⟩ : ℕ) + 1 with hm_def
  have hm : 0 < m := by omega
  apply dvd_of_div_ceil_le m k hm
  rw [← fin_card_filter_dvd m k hm, ← perm_card_filter_dvd_succ σ m]
  apply Finset.card_le_card
  intro j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  intro hj
  apply hσ m ⟨0, hk⟩ j dvd_rfl
  simp only [Nat.cast_zero, zero_sub]
  exact (dvd_neg).2 (Int.natCast_dvd_natCast.2 hj)
