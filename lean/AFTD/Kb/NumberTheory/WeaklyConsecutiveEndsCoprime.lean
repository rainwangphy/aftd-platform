import AFTD.Prelude
import AFTD.Kb.NumberTheory.IsWeaklyConsecutive
import AFTD.Kb.NumberTheory.WeaklyConsecutiveFirstDvd
import AFTD.Kb.NumberTheory.FinCardFilterDvd
import AFTD.Kb.NumberTheory.PermCardFilterDvdSucc

/-!
# weakly_consecutive_ends_coprime

Topic: elementary_number_theory   Node: c910d729c851

In a weakly consecutive sequence, the first and last terms are coprime.
-/

theorem weakly_consecutive_ends_coprime {k : ℕ} (σ : Equiv.Perm (Fin k))
    (hσ : is_weakly_consecutive σ) (hk : 0 < k) :
    Nat.Coprime ((σ ⟨0, hk⟩ : ℕ) + 1) ((σ ⟨k - 1, by omega⟩ : ℕ) + 1) := by
  apply Nat.coprime_of_dvd
  intro p hp ha hb
  have hp2 := hp.two_le
  have hpk : p ∣ k := ha.trans (weakly_consecutive_first_dvd σ hσ hk)
  have hk2 : 2 ≤ k := by
    rcases Nat.lt_or_ge k 2 with h | h
    · exfalso
      have : k = 1 := by omega
      subst this
      have h0 : (σ ⟨0, hk⟩ : ℕ) = 0 := by omega
      rw [h0] at ha
      exact hp.one_lt.ne' (Nat.dvd_one.1 ha)
    · exact h
  -- the class of position 0, plus the last position, all hold multiples of p
  set last : Fin k := ⟨k - 1, by omega⟩ with hlast
  have hsub : insert last (Finset.univ.filter fun j : Fin k => p ∣ (j : ℕ)) ⊆
      Finset.univ.filter fun j : Fin k => p ∣ (σ j : ℕ) + 1 := by
    intro j
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
    rintro (rfl | hj)
    · exact hb
    · apply hσ p ⟨0, hk⟩ j ha
      simp only [Nat.cast_zero, zero_sub]
      exact (dvd_neg).2 (Int.natCast_dvd_natCast.2 hj)
  have hnot : last ∉ (Finset.univ.filter fun j : Fin k => p ∣ (j : ℕ)) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hlast]
    intro h
    have h1 : p ∣ k - (k - 1) := Nat.dvd_sub hpk h
    have : k - (k - 1) = 1 := by omega
    rw [this] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot, fin_card_filter_dvd p k (by omega),
    perm_card_filter_dvd_succ σ p] at hc
  have : k / p ≤ (k + p - 1) / p := Nat.div_le_div_right (by omega)
  omega
