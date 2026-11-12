import AFTD.Prelude

/-!
# op223_matrix_spectral_upper

Topic: graphs   Node: 49e6dfd3a3f4

Provenance: helper lemma. arXiv:2610.17078 Open Problem 6.1; experiments 22883 and 22914

If both tI minus A and tI plus A are positive semidefinite, the real spectral radius of A is at most t.
-/

open Matrix
open scoped ENNReal

theorem op223_matrix_spectral_upper {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (t : ℝ)
    (hminus : ((algebraMap ℝ (Matrix n n ℝ)) t - A).PosSemidef)
    (hplus : ((algebraMap ℝ (Matrix n n ℝ)) t + A).PosSemidef) :
    spectralRadius ℝ A ≤ ENNReal.ofReal t := by
  unfold spectralRadius
  apply iSup_le
  intro z
  apply iSup_le
  intro hz
  have hm : 0 ≤ t - z := by
    apply (Matrix.posSemidef_iff_isHermitian_and_spectrum_nonneg.mp hminus).2
    rw [← spectrum.singleton_sub_eq]
    exact Set.sub_mem_sub (by simp) hz
  have hp : 0 ≤ t + z := by
    apply (Matrix.posSemidef_iff_isHermitian_and_spectrum_nonneg.mp hplus).2
    rw [← spectrum.singleton_add_eq]
    exact Set.add_mem_add (by simp) hz
  rw [ENNReal.coe_nnreal_eq]
  apply ENNReal.ofReal_le_ofReal
  change |z| ≤ t
  exact abs_le.mpr ⟨by linarith, by linarith⟩
