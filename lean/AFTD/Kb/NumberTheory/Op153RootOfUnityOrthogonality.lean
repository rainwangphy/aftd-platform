import AFTD.Prelude

/-!
# op_153_root_of_unity_orthogonality

Topic: elementary_number_theory   Node: c76d9d60e126

Provenance: helper lemma. step towards op_153_eventually_subexp_bound_positive_quadratic

For M > 0 and any integer k, the sum of exp(2*pi*I*n*k/M) over n = 0, 1, ..., M-1 equals M if M divides k and 0 otherwise.
-/

/-- Root-of-unity orthogonality in the finite cyclic group of order M: \u03a3_{n<M} e(nk/M) = M when M \u2223 k and 0 otherwise. -/
theorem op_153_root_of_unity_orthogonality (M : ℕ) (hM : 0 < M) (k : ℤ) :
    (∑ n ∈ Finset.range M, Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (k : ℂ) / (M : ℂ)))
      = if (M : ℤ) ∣ k then (M : ℂ) else 0 := by
  have hM_c : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hM)
  set w : ℂ := Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) / (M : ℂ)) with hw_def
  have h_term (n : ℕ) :
      Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (k : ℂ) / (M : ℂ)) = w ^ n := by
    rw [hw_def, ← Complex.exp_nat_mul]
    congr 1
    ring
  have h_sum : (∑ n ∈ Finset.range M, Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (k : ℂ) / (M : ℂ)))
      = ∑ n ∈ Finset.range M, w ^ n := by
    apply Finset.sum_congr rfl
    intro n _
    exact h_term n
  rw [h_sum]
  have hwM : w ^ M = 1 := by
    rw [hw_def, ← Complex.exp_nat_mul]
    have h_mul : (M : ℂ) * (2 * Real.pi * Complex.I * (k : ℂ) / (M : ℂ)) = (k : ℂ) * (2 * Real.pi * Complex.I) := by
      calc (M : ℂ) * (2 * Real.pi * Complex.I * (k : ℂ) / (M : ℂ))
        _ = (M : ℂ) * (2 * Real.pi * Complex.I * (k : ℂ)) / (M : ℂ) := mul_div_assoc' (M : ℂ) _ _
        _ = (2 * Real.pi * Complex.I * (k : ℂ)) * (M : ℂ) / (M : ℂ) := by ring_nf
        _ = (2 * Real.pi * Complex.I * (k : ℂ)) := mul_div_cancel_right₀ _ hM_c
        _ = (k : ℂ) * (2 * Real.pi * Complex.I) := by ring
    rw [h_mul, Complex.exp_eq_one_iff]
    exact ⟨k, rfl⟩
  have hw_iff : w = 1 ↔ (M : ℤ) ∣ k := by
    rw [hw_def, Complex.exp_eq_one_iff]
    constructor
    · rintro ⟨m, hm⟩
      have hm2 : (2 * Real.pi * Complex.I) * ((k : ℂ) / (M : ℂ)) = (2 * Real.pi * Complex.I) * (m : ℂ) := by
        calc (2 * Real.pi * Complex.I) * ((k : ℂ) / (M : ℂ))
          _ = 2 * Real.pi * Complex.I * (k : ℂ) / (M : ℂ) := by ring
          _ = (m : ℂ) * (2 * Real.pi * Complex.I) := hm
          _ = (2 * Real.pi * Complex.I) * (m : ℂ) := by ring
      have hm3 := mul_left_cancel₀ Complex.two_pi_I_ne_zero hm2
      have hm4 : (k : ℂ) = (m : ℂ) * (M : ℂ) := by
        calc (k : ℂ) = ((k : ℂ) / (M : ℂ)) * (M : ℂ) := by rw [div_mul_cancel₀ (k : ℂ) hM_c]
        _ = (m : ℂ) * (M : ℂ) := by rw [hm3]
      have hm5 : (k : ℂ) = ((m * (M : ℤ) : ℤ) : ℂ) := by
        push_cast
        exact hm4
      have hm6 : k = m * (M : ℤ) := by
        exact_mod_cast hm5
      exact ⟨m, by rw [hm6, mul_comm]⟩
    · rintro ⟨m, rfl⟩
      use m
      push_cast
      have : (M : ℂ) * (m : ℂ) / (M : ℂ) = (m : ℂ) := by
        rw [mul_div_cancel_left₀ (m : ℂ) hM_c]
      calc 2 * Real.pi * Complex.I * ((M : ℂ) * (m : ℂ)) / (M : ℂ)
        _ = (2 * Real.pi * Complex.I) * ((M : ℂ) * (m : ℂ) / (M : ℂ)) := by ring
        _ = (2 * Real.pi * Complex.I) * (m : ℂ) := by rw [this]
        _ = (m : ℂ) * (2 * Real.pi * Complex.I) := by ring
  by_cases h : (M : ℤ) ∣ k
  · rw [if_pos h]
    have hw1 : w = 1 := hw_iff.mpr h
    rw [hw1]
    simp
  · rw [if_neg h]
    have hw_ne1 : w ≠ 1 := mt hw_iff.mp h
    rw [geom_sum_eq hw_ne1 M, hwM, sub_self, zero_div]
