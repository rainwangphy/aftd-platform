import AFTD.Prelude
import AFTD.Kb.NumberTheory.Op153RootOfUnityOrthogonality

/-!
# op_153_fourier_mean_eq_constant_term

Topic: elementary_number_theory   Node: 73d61d6a5786

Provenance: helper lemma. step towards op_153_eventually_subexp_bound_positive_quadratic

For M > 0, weights phi : Z -> C supported on a finite set T containing 0, with every nonzero frequency x in T satisfying |x| < M: the average of the values sum_{x in T} phi(x)*exp(2*pi*I*x*n/M) over n = 0, ..., M-1 is the constant term phi(0).
-/

/-- The zero-th Fourier coefficient of a finitely supported trigonometric polynomial is the average of its values at the M-th roots of unity, provided no nonzero frequency is a multiple of M. -/
theorem op_153_fourier_mean_eq_constant_term (M : ℕ) (hM : 0 < M) (φ : ℤ → ℂ) (T : Finset ℤ)
    (h0 : (0 : ℤ) ∈ T) (hlt : ∀ x ∈ T, x ≠ 0 → x.natAbs < M) :
    (1 / (M : ℂ)) * (∑ n ∈ Finset.range M,
        ∑ x ∈ T, φ x * Complex.exp (2 * Real.pi * Complex.I * (x : ℂ) * (n : ℂ) / (M : ℂ))) = φ 0 := by
  have hMne : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  rw [Finset.sum_comm]
  have hinner : ∀ x ∈ T, (∑ n ∈ Finset.range M, φ x * Complex.exp (2 * Real.pi * Complex.I * (x : ℂ) * (n : ℂ) / (M : ℂ)))
      = φ x * (if (M : ℤ) ∣ x then (M : ℂ) else 0) := by
    intro x hx
    rw [← Finset.mul_sum]
    congr 1
    have hshift : (∑ n ∈ Finset.range M, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ) * (n : ℂ) / (M : ℂ)))
        = ∑ n ∈ Finset.range M, Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (x : ℂ) / (M : ℂ)) := by
      apply Finset.sum_congr rfl
      intro n hn
      congr 1
      ring
    rw [hshift, op_153_root_of_unity_orthogonality M hM x]
  rw [Finset.sum_congr rfl hinner]
  have hsingle : (∑ x ∈ T, φ x * (if (M : ℤ) ∣ x then (M : ℂ) else 0)) = φ 0 * (M : ℂ) := by
    rw [Finset.sum_eq_single (0 : ℤ)]
    · simp
    · intro b hb hb0
      have hndvd : ¬ (M : ℤ) ∣ b := by
        intro hdvd
        have hle : (M : ℤ).natAbs ≤ b.natAbs := Int.natAbs_le_of_dvd_ne_zero hdvd hb0
        have hMabs : (M : ℤ).natAbs = M := by simp
        have := hlt b hb hb0
        omega
      simp [hndvd]
    · intro h
      exact absurd h0 h
  rw [hsingle]
  rw [mul_comm (φ 0) (M : ℂ), ← mul_assoc, one_div, inv_mul_cancel₀ hMne, one_mul]
