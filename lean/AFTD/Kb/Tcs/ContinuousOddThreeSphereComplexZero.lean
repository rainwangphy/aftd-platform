import AFTD.Prelude
import AFTD.Kb.Tcs.ComplexContinuousOddCircleExtensionZero

/-!
# continuous_odd_three_sphere_complex_zero

Topic: quantum   Node: 9dc414c4f8d5

Provenance: helper lemma. arXiv:2611.19367v1, Lemma 3 (the odd-map zero); this is a standard special case of the Borsuk–Ulam theorem.

A complex-valued function continuous on the unit sphere in four real coordinates, and odd on that sphere, has a zero on the sphere.
-/

open Complex

noncomputable def in935_stereo (z : ℂ) : Fin 4 → ℝ :=
  ![2*z.re/(1+Complex.normSq z), 2*z.im/(1+Complex.normSq z),
    (1-Complex.normSq z)/(1+Complex.normSq z), 0]

lemma in935_stereo_continuous : Continuous in935_stereo := by
  have hd : ∀ z : ℂ, 1 + Complex.normSq z ≠ 0 := by
    intro z
    have h := Complex.normSq_nonneg z
    linarith
  have hdcont : Continuous (fun z : ℂ => 1 + Complex.normSq z) := by fun_prop
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun z : ℂ => 2*z.re / (1+Complex.normSq z))
    exact (continuous_const.mul Complex.continuous_re).div hdcont hd
  · change Continuous (fun z : ℂ => 2*z.im / (1+Complex.normSq z))
    exact (continuous_const.mul Complex.continuous_im).div hdcont hd
  · change Continuous (fun z : ℂ => (1-Complex.normSq z) / (1+Complex.normSq z))
    exact (by fun_prop : Continuous (fun z : ℂ => 1-Complex.normSq z)).div hdcont hd
  · change Continuous (fun _ : ℂ => (0 : ℝ))
    exact continuous_const

lemma in935_stereo_norm (z : ℂ) : (∑ i, (in935_stereo z i)^2) = 1 := by
  have hn : 1 + Complex.normSq z ≠ 0 := by have h := Complex.normSq_nonneg z; linarith
  rw [Fin.sum_univ_four]
  change (2*z.re/(1+Complex.normSq z))^2 + (2*z.im/(1+Complex.normSq z))^2 +
    ((1-Complex.normSq z)/(1+Complex.normSq z))^2 + (0 : ℝ)^2 = 1
  field_simp
  rw [Complex.normSq_apply]
  ring

lemma in935_stereo_odd (z : ℂ) (hz : Complex.normSq z = 1) :
    in935_stereo (-z) = -in935_stereo z := by
  funext i
  fin_cases i <;> simp [in935_stereo, Matrix.cons_val_three, Matrix.cons_val_two, hz] <;> ring

theorem continuous_odd_three_sphere_complex_zero (F : (Fin 4 → ℝ) → ℂ) (hF : ContinuousOn F {x | (∑ i, (x i)^2) = 1})
    (hodd : ∀ x, (∑ i, (x i)^2) = 1 → F (-x) = -F x) :
    ∃ x : Fin 4 → ℝ, (∑ i, (x i)^2) = 1 ∧ F x = 0 := by
  let g : ℂ → ℂ := fun z => F (in935_stereo z)
  have hg : Continuous g := hF.comp_continuous in935_stereo_continuous (fun z => in935_stereo_norm z)
  have hgo : ∀ z, Complex.normSq z = 1 → g (-z) = -g z := by
    intro z hz
    dsimp [g]
    rw [in935_stereo_odd z hz]
    exact hodd (in935_stereo z) (in935_stereo_norm z)
  obtain ⟨z,hz⟩ := complex_continuous_odd_circle_extension_zero g hg hgo
  exact ⟨in935_stereo z, in935_stereo_norm z, hz⟩
