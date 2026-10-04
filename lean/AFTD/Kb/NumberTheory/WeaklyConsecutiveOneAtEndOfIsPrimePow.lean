import AFTD.Prelude
import AFTD.Kb.NumberTheory.IsWeaklyConsecutive
import AFTD.Kb.NumberTheory.WeaklyConsecutiveFirstDvd
import AFTD.Kb.NumberTheory.WeaklyConsecutiveLastDvd
import AFTD.Kb.NumberTheory.WeaklyConsecutiveEndsCoprime

/-!
# weakly_consecutive_one_at_end_of_isPrimePow

Topic: elementary_number_theory   Node: f3b3f5bba7b6

Conjecture 5.2 of arXiv:2401.09497 holds when the length k is a prime power: a weakly consecutive sequence of length p^n begins or ends with 1.
-/

theorem weakly_consecutive_one_at_end_of_isPrimePow {k : ℕ} (σ : Equiv.Perm (Fin k))
    (hσ : is_weakly_consecutive σ) (hk : IsPrimePow k) (i : Fin k) (hi : (σ i : ℕ) = 0) :
    (i : ℕ) = 0 ∨ (i : ℕ) + 1 = k := by
  by_contra hne
  rw [not_or] at hne
  have hk0 : 0 < k := hk.pos
  obtain ⟨p, n, hp, hn, rfl⟩ := (isPrimePow_nat_iff _).1 hk
  -- both end values exceed 1
  have hfirst : (σ ⟨0, hk0⟩ : ℕ) ≠ 0 := by
    intro h
    have : σ ⟨0, hk0⟩ = σ i := Fin.ext (by rw [h, hi])
    have := congrArg Fin.val (σ.injective this)
    simp at this
    exact hne.1 (by omega)
  have hlast : (σ ⟨p ^ n - 1, by omega⟩ : ℕ) ≠ 0 := by
    intro h
    have : σ ⟨p ^ n - 1, by omega⟩ = σ i := Fin.ext (by rw [h, hi])
    have := congrArg Fin.val (σ.injective this)
    simp at this
    exact hne.2 (by omega)
  have ha := weakly_consecutive_first_dvd σ hσ hk0
  have hb := weakly_consecutive_last_dvd σ hσ hk0
  have hc := weakly_consecutive_ends_coprime σ hσ hk0
  obtain ⟨a, ha', hae⟩ := (Nat.dvd_prime_pow hp).1 ha
  obtain ⟨b, hb', hbe⟩ := (Nat.dvd_prime_pow hp).1 hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hae
    exact hfirst hae
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hbe
    exact hlast hbe
  rw [hae, hbe] at hc
  have hpa : p ∣ p ^ a := dvd_pow_self p ha0
  have hpb : p ∣ p ^ b := dvd_pow_self p hb0
  have h1 : Nat.Coprime p p := Nat.Coprime.coprime_dvd_left hpa (Nat.Coprime.coprime_dvd_right hpb hc)
  exact hp.one_lt.ne' ((Nat.coprime_self p).1 h1)
