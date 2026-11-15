import AFTD.Prelude

/-!
# op223_positive_vector_real_eigenvalue_bound

Topic: graphs   Node: 5aa37865efc8

Provenance: helper lemma. OP-223: spectral-radius bound from a positive vector

For a nonnegative real matrix A and strictly positive vector v with Av coordinatewise at most t times v, every real spectral value of A has absolute value at most t.
-/

lemma op223_positive_vector_real_eigenvalue_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (t : ℝ) (v : ι → ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hv : ∀ i, 0 < v i)
    (hAv : ∀ i, (A.mulVec v) i ≤ t * v i)
    (z : ℝ) (hz : z ∈ spectrum ℝ A) : |z| ≤ t := by
  classical
  have hz' : z ∈ spectrum ℝ A.toLin' := by simpa using hz
  obtain ⟨w, hw⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hz').exists_hasEigenvector
  have hwne : w ≠ 0 := (Module.End.hasEigenvector_iff.mp hw).2
  have hwcoord : ∃ j, w j ≠ 0 := by
    by_contra h
    apply hwne
    funext j
    have hj : w j = 0 := by simpa using not_exists.mp h j
    simpa using hj
  obtain ⟨j, hj⟩ := hwcoord
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image Finset.univ (fun k => |w k| / v k) ⟨j, Finset.mem_univ j⟩
  let r : ℝ := |w i| / v i
  have hr : 0 < r := lt_of_lt_of_le (div_pos (abs_pos.mpr hj) (hv j)) (hmax j (Finset.mem_univ j))
  have hratio (k : ι) : |w k| ≤ r * v k := (div_le_iff₀ (hv k)).mp (hmax k (Finset.mem_univ k))
  have hri : r * v i = |w i| := by dsimp [r]; exact div_mul_cancel₀ _ (ne_of_gt (hv i))
  have hwi : 0 < |w i| := by rw [← hri]; exact mul_pos hr (hv i)
  have heig : (∑ k, A i k * w k) = z * w i := by
    have hh := congrFun hw.apply_eq_smul i
    simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct] using hh
  have hsum : (∑ k, |A i k * w k|) ≤ r * ∑ k, A i k * v k := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    calc
      |A i k * w k| = A i k * |w k| := by rw [abs_mul, abs_of_nonneg (hA i k)]
      _ ≤ A i k * (r * v k) := mul_le_mul_of_nonneg_left (hratio k) (hA i k)
      _ = r * (A i k * v k) := by ring
  have hmul : |z| * |w i| ≤ t * |w i| := by
    calc
      |z| * |w i| = |z * w i| := (abs_mul _ _).symm
      _ = |∑ k, A i k * w k| := by rw [heig]
      _ ≤ ∑ k, |A i k * w k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ r * ∑ k, A i k * v k := hsum
      _ ≤ r * (t * v i) := mul_le_mul_of_nonneg_left (hAv i) (le_of_lt hr)
      _ = t * |w i| := by rw [← hri]; ring
  exact le_of_mul_le_mul_right hmul hwi
