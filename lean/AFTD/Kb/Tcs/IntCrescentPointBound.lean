import AFTD.Prelude
import AFTD.Kb.Tcs.IntCrescentPoint
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.IntCrescentGaussian

/-!
# int_crescent_point_bound

Topic: combinatorics   Node: d9e45b30555c

Provenance: helper lemma. arXiv:2610.38368 Section 3

For every integer n ≥ 3, every index j in Fin n, and every coordinate index i in Fin 3, the absolute value of the i-th coordinate of int_crescent_point n j is at most 2 * (n - 1) * (4 * n^2 + 1)^(n - 1).
-/

open scoped GaussianInt
open Zsqrtd

theorem int_crescent_point_bound_norm (n : ℕ) (j : Fin n) :
    norm (int_crescent_gaussian n j) = ((4 * (n : ℤ)^2 + 1) ^ (n - 1))^2 := by
  dsimp [int_crescent_gaussian]
  set B : ℤ := 4 * (n : ℤ)^2 + 1
  set w : GaussianInt := ⟨4 * (n : ℤ)^2 - 1, 4 * (n : ℤ)⟩
  have hw : norm w = B^2 := by
    simp [norm_def, w, B]
    ring
  rw [zsmul_eq_mul (w ^ (j : ℕ)) (B ^ (n - 1 - (j : ℕ)))]
  rw [norm_mul, norm_intCast]
  have hpow : norm (w ^ (j : ℕ)) = (norm w) ^ (j : ℕ) := normMonoidHom.map_pow w (j : ℕ)
  rw [hpow, hw]
  have h1 : (B ^ (j : ℕ))^2 = (B^2) ^ (j : ℕ) := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    ring
  rw [← h1]
  have h3 : B ^ (n - 1 - (j : ℕ)) * B ^ (j : ℕ) = B ^ (n - 1) := by
    rw [← pow_add]
    congr 1
    have := j.isLt
    omega
  calc B ^ (n - 1 - (j : ℕ)) * B ^ (n - 1 - (j : ℕ)) * (B ^ (j : ℕ)) ^ 2
    _ = (B ^ (n - 1 - (j : ℕ)) * B ^ (j : ℕ))^2 := by ring
    _ = (B ^ (n - 1))^2 := by rw [h3]

/-- Every coordinate of int_crescent_point n j has absolute value at most 2*(n - 1)*(4*n^2 + 1)^(n - 1). -/
theorem int_crescent_point_bound (n : ℕ) (hn : 3 ≤ n) (j : Fin n) (i : Fin 3) :
    |int_crescent_point n j i| ≤ 2 * ((n : ℤ) - 1) * (4 * (n : ℤ)^2 + 1) ^ (n - 1) := by
  have hnorm := int_crescent_point_bound_norm n j
  have hnorm_eq : Zsqrtd.norm (int_crescent_gaussian n j) =
      (int_crescent_gaussian n j).re^2 + (int_crescent_gaussian n j).im^2 := by
    simp [Zsqrtd.norm_def]
    ring
  have hB_nonneg : 0 ≤ (4 * (n : ℤ)^2 + 1) ^ (n - 1) := by positivity
  have h_bound : (4 * (n : ℤ)^2 + 1) ^ (n - 1) ≤ 2 * ((n : ℤ) - 1) * (4 * (n : ℤ)^2 + 1) ^ (n - 1) := by
    calc (4 * (n : ℤ)^2 + 1) ^ (n - 1)
      _ = 1 * (4 * (n : ℤ)^2 + 1) ^ (n - 1) := by ring
      _ ≤ 2 * ((n : ℤ) - 1) * (4 * (n : ℤ)^2 + 1) ^ (n - 1) := by
        apply mul_le_mul_of_nonneg_right _ hB_nonneg
        omega
  fin_cases i
  · -- i = 0
    change |(int_crescent_gaussian n j).re| ≤ _
    have hre_sq : (int_crescent_gaussian n j).re^2 ≤ ((4 * (n : ℤ)^2 + 1) ^ (n - 1))^2 := by
      rw [← hnorm, hnorm_eq]
      have : 0 ≤ (int_crescent_gaussian n j).im^2 := sq_nonneg _
      linarith
    have h_abs : |(int_crescent_gaussian n j).re| ≤ (4 * (n : ℤ)^2 + 1) ^ (n - 1) := by
      have := sq_le_sq.mp hre_sq
      rwa [abs_of_nonneg hB_nonneg] at this
    exact h_abs.trans h_bound
  · -- i = 1
    change |(int_crescent_gaussian n j).im| ≤ _
    have him_sq : (int_crescent_gaussian n j).im^2 ≤ ((4 * (n : ℤ)^2 + 1) ^ (n - 1))^2 := by
      rw [← hnorm, hnorm_eq]
      have : 0 ≤ (int_crescent_gaussian n j).re^2 := sq_nonneg _
      linarith
    have h_abs : |(int_crescent_gaussian n j).im| ≤ (4 * (n : ℤ)^2 + 1) ^ (n - 1) := by
      have := sq_le_sq.mp him_sq
      rwa [abs_of_nonneg hB_nonneg] at this
    exact h_abs.trans h_bound
  · -- i = 2
    change |2 * (j : ℤ) * (4 * (n : ℤ)^2 + 1) ^ (n - 1)| ≤ _
    have hj : (j : ℤ) ≤ (n : ℤ) - 1 := by
      have := j.isLt
      omega
    have hterm0 : 0 ≤ 2 * (j : ℤ) * (4 * (n : ℤ)^2 + 1) ^ (n - 1) := by positivity
    rw [abs_of_nonneg hterm0]
    nlinarith
