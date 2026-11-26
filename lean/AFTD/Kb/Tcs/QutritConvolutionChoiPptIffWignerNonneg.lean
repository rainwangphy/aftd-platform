import AFTD.Prelude
import AFTD.Kb.Tcs.QutritConvolutionChoi
import AFTD.Kb.Tcs.C

/-!
# qutrit_convolution_choi_ppt_iff_wigner_nonneg

Topic: quantum   Node: 9fcf88ca5292

Provenance: original. Related work: OP-2299; the screen's signal on it (experiments 39257-39263, reproduced in experiment 39657): the partial transpose of the Choi matrix of the qutrit convolution channel is diagonal in the Weyl-Bell basis with the discrete Wigner function of the environment as eigenvalues. That convolution channels with a Wigner-positive environment are PPT is the starting point of the convolution-channel work the entry builds on; this is the exact two-sided form for one qutrit.

Let σ : Matrix (Fin 3) (Fin 3) ℂ be Hermitian (σ.IsHermitian) and let ω = exp(2πi/3). The partial transpose on the second factor of qutrit_convolution_choi σ, i.e. the matrix indexed by Fin 3 × Fin 3 whose (p, q) entry is qutrit_convolution_choi σ (p.1, q.2) (q.1, p.2), is positive semidefinite if and only if for all c, p in Fin 3 the real part of Σ_{t : Fin 3} ω^(p.val * t.val) * σ(c − t, c + t) is nonnegative (indices of σ computed in Fin 3, i.e. modulo 3). The nine numbers (1/3) Σ_t ω^{pt} σ(c−t, c+t) are the values of the discrete Wigner function of σ, so the Choi matrix is PPT exactly when the environment σ has a nonnegative discrete Wigner function.
-/

theorem in1187_circ (w g0 g1 g2 u0 u1 u2 s0 s1 s2 : ℂ) (h : 1 + w + w ^ 2 = 0) :
    3 * (s0 * (g0 * u0 + g2 * u1 + g1 * u2) + s1 * (g1 * u0 + g0 * u1 + g2 * u2) +
        s2 * (g2 * u0 + g1 * u1 + g0 * u2)) =
      (g0 + g1 + g2) * (s0 + s1 + s2) * (u0 + u1 + u2) +
      (g0 + w * g1 + w ^ 2 * g2) * (s0 + w ^ 2 * s1 + w ^ 4 * s2) * (u0 + w * u1 + w ^ 2 * u2) +
      (g0 + w ^ 2 * g1 + w ^ 4 * g2) * (s0 + w ^ 4 * s1 + w ^ 8 * s2) *
        (u0 + w ^ 2 * u1 + w ^ 4 * u2) := by
  linear_combination (-g0*s0*u1 - g0*s0*u2 - g0*s1*u0 + 2*g0*s1*u1 - g0*s1*u2 - g0*s2*u0 - g0*s2*u1 + 2*g0*s2*u2 - g1*s0*u0 - g1*s0*u1 + 2*g1*s0*u2 + 2*g1*s1*u0 - g1*s1*u1 - g1*s1*u2 - g1*s2*u0 + 2*g1*s2*u1 - g1*s2*u2 - g2*s0*u0 + 2*g2*s0*u1 - g2*s0*u2 - g2*s1*u0 - g2*s1*u1 + 2*g2*s1*u2 + 2*g2*s2*u0 - g2*s2*u1 - g2*s2*u2*w^14 + g2*s2*u2*w^13 - g2*s2*u2 + w^12*(-g1*s2*u2 - g2*s2*u1) + w^11*(g1*s2*u2 + g2*s2*u1 - g2*s2*u2) + w^10*(-g0*s2*u2 - g1*s2*u1 - g2*s1*u2 - g2*s2*u0 + g2*s2*u2) + w^9*(g0*s2*u2 + g1*s2*u1 - g1*s2*u2 + g2*s1*u2 + g2*s2*u0 - g2*s2*u1) + w^8*(-g0*s2*u1 - g1*s1*u2 - g1*s2*u0 + g1*s2*u2 - g2*s1*u1 + g2*s2*u1 - g2*s2*u2) + w^7*(g0*s2*u1 - g0*s2*u2 + g1*s1*u2 + g1*s2*u0 - g1*s2*u1 + g2*s1*u1 - g2*s1*u2 - g2*s2*u0 + g2*s2*u2) + w^6*(-g0*s1*u2 - g0*s2*u0 + g0*s2*u2 - g1*s1*u1 + g1*s2*u1 - g1*s2*u2 - g2*s0*u2 - g2*s1*u0 + g2*s1*u2 + g2*s2*u0 - g2*s2*u1 - g2*s2*u2) + w^5*(g0*s1*u2 + g0*s2*u0 - g0*s2*u1 + g1*s1*u1 - g1*s1*u2 - g1*s2*u0 + g2*s0*u2 + g2*s1*u0 - g2*s1*u1) + w^4*(-g0*s1*u1 + g0*s2*u1 - 2*g0*s2*u2 - g1*s0*u2 - g1*s1*u0 + g1*s1*u2 + g1*s2*u0 - 2*g1*s2*u1 + g1*s2*u2 - g2*s0*u1 + g2*s1*u1 - 2*g2*s1*u2 - 2*g2*s2*u0 + g2*s2*u1 + g2*s2*u2) + w^3*(g0*s1*u1 - g0*s1*u2 - g0*s2*u0 - g0*s2*u1 + 2*g0*s2*u2 + g1*s0*u2 + g1*s1*u0 - g1*s1*u1 - g1*s1*u2 - g1*s2*u0 + 2*g1*s2*u1 - g1*s2*u2 + g2*s0*u1 - g2*s0*u2 - g2*s1*u0 - g2*s1*u1 + 2*g2*s1*u2 + 2*g2*s2*u0 - g2*s2*u1 - g2*s2*u2) + w^2*(-g0*s0*u2 - g0*s1*u0 - g1*s0*u1 - g2*s0*u0) + w*(g0*s0*u2 + g0*s1*u0 - 2*g0*s1*u1 + g0*s1*u2 + g0*s2*u0 + g0*s2*u1 - 2*g0*s2*u2 + g1*s0*u1 - 2*g1*s0*u2 - 2*g1*s1*u0 + g1*s1*u1 + g1*s1*u2 + g1*s2*u0 - 2*g1*s2*u1 + g1*s2*u2 + g2*s0*u0 - 2*g2*s0*u1 + g2*s0*u2 + g2*s1*u0 + g2*s1*u1 - 2*g2*s1*u2 - 2*g2*s2*u0 + g2*s2*u1 + g2*s2*u2)) * h

theorem in1187_qf (σ : Matrix (Fin 3) (Fin 3) ℂ) (w : ℂ) (h : 1 + w + w ^ 2 = 0)
    (s x : Fin 3 × Fin 3 → ℂ) :
    9 * (s ⬝ᵥ (Matrix.of fun (p q : Fin 3 × Fin 3) =>
        qutrit_convolution_choi σ (p.1, q.2) (q.1, p.2)).mulVec x) =
      ∑ c : Fin 3, ∑ p : Fin 3, (∑ t : Fin 3, w ^ (p.val * t.val) * σ (c - t) (c + t)) *
        ((∑ a : Fin 3, w ^ (2 * p.val * a.val) * s (a, a + c)) *
          (∑ a : Fin 3, w ^ (p.val * a.val) * x (a, a + c))) := by
  have h1 : (-1 : Fin 3) = 2 := rfl
  have h2 : (-2 : Fin 3) = 1 := rfl
  simp [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Fin.sum_univ_three,
    qutrit_convolution_choi, h1, h2]
  linear_combination
    in1187_circ w (σ 0 0) (σ 2 1) (σ 1 2) (x (0, 0)) (x (1, 1)) (x (2, 2))
      (s (0, 0)) (s (1, 1)) (s (2, 2)) h +
    in1187_circ w (σ 1 1) (σ 0 2) (σ 2 0) (x (0, 1)) (x (1, 2)) (x (2, 0))
      (s (0, 1)) (s (1, 2)) (s (2, 0)) h +
    in1187_circ w (σ 2 2) (σ 1 0) (σ 0 1) (x (0, 2)) (x (1, 0)) (x (2, 1))
      (s (0, 2)) (s (1, 0)) (s (2, 1)) h

theorem in1187_orth (w : ℂ) (h : 1 + w + w ^ 2 = 0) (ℓ : Fin 3 → ℂ) (p : Fin 3) :
    ∑ p' : Fin 3, ℓ p' * ((∑ a : Fin 3, w ^ (2 * p'.val * a.val) * w ^ (p.val * a.val)) *
      (∑ a : Fin 3, w ^ (p'.val * a.val) * w ^ (2 * p.val * a.val))) = 9 * ℓ p := by
  fin_cases p
  · simp [Fin.sum_univ_three]
    linear_combination (ℓ 1 + ℓ 2*w^10 - ℓ 2*w^9 + ℓ 2*w^8 + ℓ 2*w^6 - ℓ 2*w^5 - ℓ 2*w + ℓ 2 + w^4*(ℓ 1 + ℓ 2) + w^2*(ℓ 1 + ℓ 2)) * h
  · simp [Fin.sum_univ_three]
    linear_combination (ℓ 0*w^2 + ℓ 0 + ℓ 1*w^10 - ℓ 1*w^9 + 3*ℓ 1*w^7 - 3*ℓ 1*w^6 - 8*ℓ 1 + ℓ 2*w^16 - ℓ 2*w^15 + ℓ 2*w^13 + ℓ 2*w^8 + ℓ 2 + w^4*(ℓ 0 + 6*ℓ 1) + w^3*(-6*ℓ 1 + ℓ 2) + w*(8*ℓ 1 - ℓ 2)) * h
  · simp [Fin.sum_univ_three]
    linear_combination (-ℓ 0*w^5 + ℓ 0*w^2 + ℓ 0 + ℓ 1 + ℓ 2*w^22 - ℓ 2*w^21 + ℓ 2*w^19 - ℓ 2*w^18 - 3*ℓ 2*w^12 + 6*ℓ 2*w^7 - 8*ℓ 2 + w^16*(ℓ 1 + 3*ℓ 2) + w^15*(-ℓ 1 - 3*ℓ 2) + w^13*(ℓ 1 + 3*ℓ 2) + w^10*(ℓ 0 + 6*ℓ 2) + w^9*(-ℓ 0 - 6*ℓ 2) + w^8*(ℓ 0 + ℓ 1) + w^6*(ℓ 0 - 6*ℓ 2) + w^4*(ℓ 0 + 8*ℓ 2) + w^3*(ℓ 1 - 8*ℓ 2) + w*(-ℓ 0 - ℓ 1 + 8*ℓ 2)) * h

theorem qutrit_convolution_choi_ppt_iff_wigner_nonneg (σ : Matrix (Fin 3) (Fin 3) ℂ)
    (hσ : σ.IsHermitian) :
    open scoped ComplexOrder in
    (Matrix.of fun (p q : Fin 3 × Fin 3) =>
        qutrit_convolution_choi σ (p.1, q.2) (q.1, p.2)).PosSemidef ↔
      ∀ c p : Fin 3, 0 ≤ (∑ t : Fin 3,
        Complex.exp (2 * Real.pi * Complex.I / 3) ^ (p.val * t.val) * σ (c - t) (c + t)).re := by
  open scoped ComplexOrder in
  set w : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3) with hw
  have hw3 : w ^ 3 = 1 := by
    rw [hw, ← Complex.exp_nat_mul]
    convert Complex.exp_two_pi_mul_I using 2
    push_cast; ring
  have hw1 : w ≠ 1 := by
    intro h
    rw [hw, Complex.exp_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero]
    have h0 : (2 * (Real.pi : ℂ) * Complex.I) * (1 - 3 * (n : ℂ)) = 0 := by
      linear_combination 3 * hn
    rcases mul_eq_zero.1 h0 with h' | h'
    · exact hpi h'
    · have h3 : (1 : ℂ) = 3 * (n : ℂ) := by linear_combination h'
      have h4 : (1 : ℤ) = 3 * n := by exact_mod_cast h3
      omega
  have h : 1 + w + w ^ 2 = 0 := by
    have h0 : (w - 1) * (1 + w + w ^ 2) = 0 := by linear_combination hw3
    rcases mul_eq_zero.1 h0 with h' | h'
    · exact absurd (sub_eq_zero.1 h') hw1
    · exact h'
  have hs : star w = w ^ 2 := by
    have e1 : star w = w⁻¹ := by
      have hz : (2 * (Real.pi : ℂ) * Complex.I / 3) =
          ((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [hw, hz, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_neg, map_mul,
        Complex.conj_ofReal, Complex.conj_I]
      congr 1
      ring
    have hne : w ≠ 0 := by rw [hw]; exact Complex.exp_ne_zero _
    rw [e1]
    field_simp
    linear_combination -hw3
  have hσ' : ∀ i j, star (σ i j) = σ j i := fun i j => hσ.apply j i
  have hstar : ∀ c p : Fin 3, star (∑ t : Fin 3, w ^ (p.val * t.val) * σ (c - t) (c + t)) =
      ∑ t : Fin 3, w ^ (p.val * t.val) * σ (c - t) (c + t) := by
    intro c p
    have e2 : c - 2 = c + 1 := by fin_cases c <;> rfl
    have e3 : c + 2 = c - 1 := by fin_cases c <;> rfl
    have h4 : w ^ (4 * p.val) = w ^ p.val := by
      rw [show 4 * p.val = p.val + 3 * p.val by ring, pow_add, pow_mul, hw3, one_pow, mul_one]
    simp only [Fin.sum_univ_three, star_add, star_mul', star_pow, hs, hσ', ← pow_mul,
      Fin.val_zero, Fin.val_one, Fin.val_two, sub_zero, add_zero, e2, e3]
    linear_combination (σ (c - 1) (c + 1)) * h4
  have hreal : ∀ c p : Fin 3, (∑ t : Fin 3, w ^ (p.val * t.val) * σ (c - t) (c + t)) =
      (((∑ t : Fin 3, w ^ (p.val * t.val) * σ (c - t) (c + t)).re : ℝ) : ℂ) := by
    intro c p
    have him := Complex.conj_eq_iff_im.1 (hstar c p)
    exact Complex.ext (by simp) (by simpa using him)
  have herm : (Matrix.of fun (p q : Fin 3 × Fin 3) =>
        qutrit_convolution_choi σ (p.1, q.2) (q.1, p.2)).IsHermitian := by
    ext ⟨a, b⟩ ⟨a', b'⟩
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, qutrit_convolution_choi]
    by_cases hc : a + b' = a' + b
    · rw [if_pos hc, if_pos hc.symm, star_div₀, hσ']; simp
    · rw [if_neg hc, if_neg (fun h' => hc h'.symm)]; simp
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · rintro ⟨-, hpos⟩ c p
    have hx := hpos (fun q : Fin 3 × Fin 3 => if q.2 - q.1 = c then w ^ (2 * p.val * q.1.val) else 0)
    have hsx : star (fun q : Fin 3 × Fin 3 => if q.2 - q.1 = c then w ^ (2 * p.val * q.1.val) else 0)
        = fun q : Fin 3 × Fin 3 => if q.2 - q.1 = c then w ^ (p.val * q.1.val) else 0 := by
      funext q
      rw [Pi.star_apply]
      split_ifs
      · have h31 : w ^ (3 * (p.val * q.1.val)) = 1 := by rw [pow_mul, hw3, one_pow]
        rw [star_pow, hs, ← pow_mul,
          show 2 * (2 * p.val * q.1.val) = p.val * q.1.val + 3 * (p.val * q.1.val) by ring,
          pow_add, h31, mul_one]
      · simp
    rw [hsx] at hx
    have key := in1187_qf σ w h
      (fun q : Fin 3 × Fin 3 => if q.2 - q.1 = c then w ^ (p.val * q.1.val) else 0)
      (fun q : Fin 3 × Fin 3 => if q.2 - q.1 = c then w ^ (2 * p.val * q.1.val) else 0)
    have hcc : ∀ a c' : Fin 3, (a + c' - a = c) ↔ c = c' := by
      intro a c'; rw [add_sub_cancel_left]; exact eq_comm
    simp only [hcc, mul_ite, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero, ite_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true] at key
    rw [in1187_orth w h (fun p' => ∑ t : Fin 3, w ^ (p'.val * t.val) * σ (c - t) (c + t)) p] at key
    have h9 : (0 : ℂ) ≤ ((9 : ℝ) : ℂ) * (∑ t : Fin 3, w ^ (p.val * t.val) * σ (c - t) (c + t)) := by
      have h90 : (0 : ℂ) ≤ 9 * (∑ t : Fin 3, w ^ (p.val * t.val) * σ (c - t) (c + t)) := by
        rw [← key]
        exact mul_nonneg (by norm_num) hx
      simpa using h90
    have h9r := (Complex.nonneg_iff.1 h9).1
    rw [Complex.re_ofReal_mul] at h9r
    linarith
  · intro hL0
    refine ⟨herm, fun x => ?_⟩
    have key := in1187_qf σ w h (star x) x
    have e9 : star x ⬝ᵥ (Matrix.of fun (p q : Fin 3 × Fin 3) =>
        qutrit_convolution_choi σ (p.1, q.2) (q.1, p.2)).mulVec x =
        (((1 / 9 : ℝ)) : ℂ) * (9 * (star x ⬝ᵥ (Matrix.of fun (p q : Fin 3 × Fin 3) =>
        qutrit_convolution_choi σ (p.1, q.2) (q.1, p.2)).mulVec x)) := by
      push_cast; ring
    rw [e9, key]
    refine mul_nonneg (Complex.zero_le_real.2 (by norm_num))
      (Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun p _ => ?_)
    rw [hreal c p]
    refine mul_nonneg (Complex.zero_le_real.2 (hL0 c p)) ?_
    have hv : (∑ a : Fin 3, w ^ (2 * p.val * a.val) * star x (a, a + c)) =
        star (∑ a : Fin 3, w ^ (p.val * a.val) * x (a, a + c)) := by
      rw [star_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [star_mul', star_pow, hs, ← pow_mul, Pi.star_apply, mul_assoc]
    rw [hv]
    exact star_mul_self_nonneg _
