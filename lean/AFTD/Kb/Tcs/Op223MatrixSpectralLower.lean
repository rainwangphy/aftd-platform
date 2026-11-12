import AFTD.Prelude
import AFTD.Kb.Tcs.Op223MatrixSpectrumAbsLe
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Physics.LinearPMapIsSelfAdjointSmul

/-!
# op223_matrix_spectral_lower

Topic: graphs   Node: 6fe9c3654eb9

Provenance: helper lemma. arXiv:2610.17078 Open Problem 6.1; experiments 22883 and 22914

A negative quadratic form for tI minus a Hermitian real matrix certifies that its real spectral radius exceeds t.
-/

open Matrix
open scoped ENNReal

theorem op223_matrix_spectral_lower {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (t : ℝ) (ht : 0 ≤ t)
    (v : n → ℝ)
    (hv : star v ⬝ᵥ (((algebraMap ℝ (Matrix n n ℝ)) t - A) *ᵥ v) < 0) :
    ENNReal.ofReal t < spectralRadius ℝ A := by
  by_contra hn
  have hs := op223_matrix_spectrum_abs_le A t ht (le_of_not_gt hn)
  have hPSD : ((algebraMap ℝ (Matrix n n ℝ)) t - A).PosSemidef := by
    apply Matrix.posSemidef_iff_isHermitian_and_spectrum_nonneg.mpr
    constructor
    · rw [Algebra.algebraMap_eq_smul_one]
      exact (Matrix.isHermitian_one.smul (by simp [isSelfAdjoint_iff] : IsSelfAdjoint t)).sub hA
    · intro z hz
      rw [← spectrum.singleton_sub_eq] at hz
      obtain ⟨a, ha, b, hb, rfl⟩ := hz
      simp only [Set.mem_singleton_iff] at ha
      subst a
      have := hs b hb
      change 0 ≤ t - b
      linarith [abs_le.mp this]
  linarith [hPSD.dotProduct_mulVec_nonneg v]
