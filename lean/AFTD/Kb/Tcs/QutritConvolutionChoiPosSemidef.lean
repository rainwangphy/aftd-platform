import AFTD.Prelude
import AFTD.Kb.Tcs.QutritConvolutionChoi

/-!
# qutrit_convolution_choi_pos_semidef

Topic: quantum   Node: f9b114ae6d11

Provenance: helper lemma. Sanity lemma for the definition qutrit_convolution_choi, serving OP-2299: the Choi matrix of a completely positive map is positive semidefinite.

If the complex 3×3 matrix σ is positive semidefinite then qutrit_convolution_choi σ is positive semidefinite.
-/

theorem qutrit_convolution_choi_pos_semidef (σ : Matrix (Fin 3) (Fin 3) ℂ)
    (hσ : open scoped ComplexOrder in σ.PosSemidef) :
    open scoped ComplexOrder in (qutrit_convolution_choi σ).PosSemidef := by
  open scoped ComplexOrder in
  have key : qutrit_convolution_choi σ = ∑ s : Fin 3,
      (Matrix.of fun (p : Fin 3 × Fin 3) (y : Fin 3) =>
        if p.1 + p.2 = s ∧ p.2 - p.1 = y then (1 : ℂ) else 0) * ((1 / 3 : ℝ) • σ) *
      (Matrix.of fun (p : Fin 3 × Fin 3) (y : Fin 3) =>
        if p.1 + p.2 = s ∧ p.2 - p.1 = y then (1 : ℂ) else 0).conjTranspose := by
    have h1 : (-1 : Fin 3) = 2 := rfl
    have h2 : (-2 : Fin 3) = 1 := rfl
    ext ⟨a, b⟩ ⟨a', b'⟩
    simp only [qutrit_convolution_choi, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.smul_apply, Fin.sum_univ_three]
    fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
      simp (decide := true) <;> (try simp only [h1, h2]) <;> ring
  rw [key]
  exact Matrix.posSemidef_sum _ fun s _ => (hσ.smul (by norm_num : (0 : ℝ) ≤ 1 / 3)).mul_mul_conjTranspose_same _
