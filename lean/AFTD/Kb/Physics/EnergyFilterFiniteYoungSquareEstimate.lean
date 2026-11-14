import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterFiniteCubeProductCs

/-!
# energy_filter_finite_young_square_estimate

Topic: statistical_mechanics   Node: 7c510ea41744

Provenance: helper lemma. OP-892: convolution and quartic-cycle summability.

For finite real sequences u and v whose fourth-power sums are each at most a nonnegative A, the square of the sum of u³v³ is at most A times the sum of u⁴v⁴.
-/

theorem energy_filter_finite_young_square_estimate
    {ι : Type*} (s : Finset ι) (u v : ι → ℝ) (A : ℝ)
    (hA : 0 ≤ A)
    (hu : (∑ i ∈ s, u i ^ 4) ≤ A) (hv : (∑ i ∈ s, v i ^ 4) ≤ A) :
    (∑ i ∈ s, u i ^ 3 * v i ^ 3) ^ 2 ≤
      A * (∑ i ∈ s, u i ^ 4 * v i ^ 4) := by
  let S := ∑ i ∈ s, u i ^ 3 * v i ^ 3
  let B := ∑ i ∈ s, u i ^ 4 * v i ^ 4
  let U := ∑ i ∈ s, u i ^ 4
  let V := ∑ i ∈ s, v i ^ 4
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have huv : U * V ≤ A * A := mul_le_mul hu hv hV hA
  have h4 : S^4 ≤ B^2 * U * V := energy_filter_finite_cube_product_cs s u v
  have hsquare : (S^2)^2 ≤ (A*B)^2 := by
    have hmul := mul_le_mul_of_nonneg_left huv (sq_nonneg B)
    nlinarith [h4, hmul]
  exact (sq_le_sq₀ (sq_nonneg S) (mul_nonneg hA hB)).mp hsquare
