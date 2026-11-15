import AFTD.Prelude
import AFTD.Kb.Tcs.Op223PositiveVectorRealEigenvalueBound

/-!
# op223_nonnegative_spectral_radius_le_of_positive_vector

Topic: graphs   Node: a9e71ab2790e

Provenance: helper lemma. Standard positive-vector spectral-radius bound for nonnegative matrices.

A nonnegative real matrix has spectral radius at most t when it sends a strictly positive vector coordinatewise below t times that vector.
-/

theorem op223_nonnegative_spectral_radius_le_of_positive_vector {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (t : ℝ) (v : ι → ℝ) (ht : 0 ≤ t)
    (hA : ∀ i j, 0 ≤ A i j) (hv : ∀ i, 0 < v i)
    (hAv : ∀ i, (A.mulVec v) i ≤ t * v i) : spectralRadius ℝ A ≤ ENNReal.ofReal t := by
  unfold spectralRadius
  apply iSup_le
  intro z
  apply iSup_le
  intro hz
  rw [ENNReal.coe_nnreal_eq]
  apply ENNReal.ofReal_le_ofReal
  change |z| ≤ t
  exact op223_positive_vector_real_eigenvalue_bound A t v hA hv hAv z hz
