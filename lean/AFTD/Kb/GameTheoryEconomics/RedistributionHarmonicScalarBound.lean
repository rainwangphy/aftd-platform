import AFTD.Prelude

/-!
# redistribution_harmonic_scalar_bound

Topic: mechanism_design   Node: 18f4c28691e7

Provenance: helper lemma. Uniform helper for IN-251, the proof of arXiv:2610.10995 Lemmas4.2/4.3. The disk logarithmic mean theorem and logarithm series already exist in the installed Mathlib; the upper-half-plane boundary passage, singular cosine integral and main harmonic bound remain unresolved. No research advance.

For every natural m and real y with 0<=y<1, harmonic(m) times y^m is at most -log(1-y). This is the scalar multiplier estimate in the published harmonic trade-error proof.
-/

open Finset Real MeasureTheory Metric MeromorphicOn

theorem redistribution_harmonic_scalar_bound
    (m : ℕ) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    (harmonic m : ℝ) * y^m ≤ -Real.log (1-y) := by
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one (x := y)
    (by simpa only [abs_of_nonneg hy0] using hy1)
  have hf : (harmonic m : ℝ) = ∑ i ∈ range m, (1 / ((i+1 : ℕ) : ℝ)) := by
    simp [harmonic]
  rw [hf, sum_mul]
  calc
    _ ≤ ∑ i ∈ range m, y^(i+1) / ((i+1 : ℕ) : ℝ) := by
      apply sum_le_sum
      intro i hi
      have hp := pow_le_pow_of_le_one hy0 hy1.le (by simpa using hi : i+1 ≤ m)
      simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using
        mul_le_mul_of_nonneg_right hp (by positivity : 0 ≤ (((i+1 : ℕ) : ℝ))⁻¹)
    _ ≤ -Real.log (1-y) := by
      have ht := hs.summable.sum_le_tsum (range m)
        (fun i _ => div_nonneg (pow_nonneg hy0 _) (by positivity))
      simpa only [hs.tsum_eq, Nat.cast_add, Nat.cast_one] using ht
