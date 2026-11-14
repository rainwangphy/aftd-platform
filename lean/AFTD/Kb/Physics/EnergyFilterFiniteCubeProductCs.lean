import AFTD.Prelude

/-!
# energy_filter_finite_cube_product_cs

Topic: statistical_mechanics   Node: 8392f1e4fa02

Provenance: helper lemma. OP-892: finite Cauchy–Schwarz step toward the ℓ^(4/3) convolution bound.

For any finite set and real functions u and v, the fourth power of the sum of u cubed times v cubed is at most the product of the square of the sum of u to the fourth times v to the fourth, the sum of u to the fourth, and the sum of v to the fourth.
-/

theorem energy_filter_finite_cube_product_cs {ι : Type*} (s : Finset ι) (u v : ι → ℝ) :
    (∑ i ∈ s, u i ^ 3 * v i ^ 3) ^ 4 ≤
      (∑ i ∈ s, u i ^ 4 * v i ^ 4) ^ 2 *
        (∑ i ∈ s, u i ^ 4) * (∑ i ∈ s, v i ^ 4) := by
  let A := ∑ i ∈ s, u i ^ 3 * v i ^ 3
  let B := ∑ i ∈ s, u i ^ 4 * v i ^ 4
  let D := ∑ i ∈ s, u i ^ 2 * v i ^ 2
  let U := ∑ i ∈ s, u i ^ 4
  let V := ∑ i ∈ s, v i ^ 4
  have h1 : A ^ 2 ≤ B * D := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => u i ^ 2 * v i ^ 2) (fun i => u i * v i)
    have hleft : (∑ i ∈ s, (u i ^ 2 * v i ^ 2) * (u i * v i)) = A := by
      dsimp [A]; apply Finset.sum_congr rfl; intro i hi; ring
    have hright1 : (∑ i ∈ s, (u i ^ 2 * v i ^ 2) ^ 2) = B := by
      dsimp [B]; apply Finset.sum_congr rfl; intro i hi; ring
    have hright2 : (∑ i ∈ s, (u i * v i) ^ 2) = D := by
      dsimp [D]; apply Finset.sum_congr rfl; intro i hi; ring
    rw [hleft, hright1, hright2] at h
    exact h
  have h2 : D ^ 2 ≤ U * V := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => u i ^ 2) (fun i => v i ^ 2)
    have hleft : (∑ i ∈ s, u i ^ 2 * v i ^ 2) = D := rfl
    have hright1 : (∑ i ∈ s, (u i ^ 2) ^ 2) = U := by
      dsimp [U]; apply Finset.sum_congr rfl; intro i hi; ring
    have hright2 : (∑ i ∈ s, (v i ^ 2) ^ 2) = V := by
      dsimp [V]; apply Finset.sum_congr rfl; intro i hi; ring
    rw [hleft, hright1, hright2] at h
    exact h
  have hB : 0 ≤ B := by
    dsimp [B]; apply Finset.sum_nonneg; intro i hi; positivity
  have hD : 0 ≤ D := by
    dsimp [D]; exact Finset.sum_nonneg (fun i hi => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hBD : 0 ≤ B * D := mul_nonneg hB hD
  calc
    A ^ 4 = (A ^ 2) ^ 2 := by ring
    _ ≤ (B * D) ^ 2 := (sq_le_sq₀ (sq_nonneg A) hBD).2 h1
    _ = B ^ 2 * D ^ 2 := by ring
    _ ≤ B ^ 2 * (U * V) := mul_le_mul_of_nonneg_left h2 (sq_nonneg B)
    _ = B ^ 2 * U * V := by ring
