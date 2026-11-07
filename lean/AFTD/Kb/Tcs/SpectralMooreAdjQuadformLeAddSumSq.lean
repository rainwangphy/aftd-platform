import AFTD.Prelude
import AFTD.Kb.Tcs.SpectralMooreAdjQuadformLeOfSumEqZero
import AFTD.Kb.Tcs.SpectralMooreSecondEigenvalueLe

/-!
# spectral_moore_adj_quadform_le_add_sum_sq

Topic: graphs   Node: 0dded60c6876

Provenance: helper lemma. arXiv:2611.00591 (A spectral Moore problem and the Yang-Koolen conjecture), Section 5, the positive semidefiniteness of M = I + αS_G in (11)

For a k-regular finite simple graph G on a vertex type V with second largest adjacency eigenvalue at most θ and k ≤ θ + |V|/2, every x : V → ℝ satisfies x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) ≤ θ * (x ⬝ᵥ x) + (∑ v, x v)^2 / 2; that is, θI + J/2 - A_G is positive semidefinite.
-/

open Classical SimpleGraph Matrix in
theorem spectral_moore_adj_quadform_le_add_sum_sq {V : Type*} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) (θ : ℝ) (hreg : G.IsRegularOfDegree k)
    (hθ : spectral_moore_second_eigenvalue_le G θ)
    (hk : (k : ℝ) ≤ θ + (Fintype.card V : ℝ) / 2) (x : V → ℝ) :
    x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) ≤ θ * (x ⬝ᵥ x) + (∑ v, x v) ^ 2 / 2 := by
  rcases Nat.eq_zero_or_pos (Fintype.card V) with hn | hn
  · have : IsEmpty V := Fintype.card_eq_zero_iff.mp hn
    simp [dotProduct]
  have hn' : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  set A := G.adjMatrix ℝ with hA
  set one : V → ℝ := fun _ => 1 with hone
  set c : ℝ := (∑ v, x v) / Fintype.card V with hc
  set z : V → ℝ := x - c • one with hzdef
  have hz : ∑ v, z v = 0 := by
    simp only [hzdef, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hone, mul_one,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc]
    field_simp; ring
  have hqz := spectral_moore_adj_quadform_le_of_sum_eq_zero G k θ hreg hθ z hz
  have hx : x = z + c • one := by simp [hzdef]
  have h1 : A *ᵥ one = fun _ => (k : ℝ) := by
    funext v
    simp only [hA, hone, adjMatrix_mulVec_apply, Finset.sum_const, card_neighborFinset_eq_degree,
      hreg.degree_eq, nsmul_eq_mul, mul_one]
  have hAsymm : ∀ x y : V → ℝ, x ⬝ᵥ (A *ᵥ y) = (A *ᵥ x) ⬝ᵥ y := by
    intro x y
    rw [dotProduct_mulVec, ← mulVec_transpose, (G.isSymm_adjMatrix (α := ℝ)).eq, dotProduct_comm]
  have z_one : z ⬝ᵥ one = 0 := by simp [dotProduct, hone, hz]
  have one_z : one ⬝ᵥ z = 0 := by rw [dotProduct_comm]; exact z_one
  have one_A_z : one ⬝ᵥ (A *ᵥ z) = 0 := by
    rw [hAsymm, h1]; simp [dotProduct, ← Finset.mul_sum, hz]
  have z_A_one : z ⬝ᵥ (A *ᵥ one) = 0 := by rw [hAsymm, dotProduct_comm, one_A_z]
  have one_A_one : one ⬝ᵥ (A *ᵥ one) = k * Fintype.card V := by
    rw [h1]; simp [dotProduct, hone, mul_comm]
  have one_one : one ⬝ᵥ one = Fintype.card V := by
    simp only [hone, dotProduct, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hsum : ∑ v, x v = c * Fintype.card V := by
    rw [hc]; field_simp
  rw [hsum, hx]
  simp only [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, one_A_z, z_A_one, z_one, one_z, one_A_one, one_one]
  have hc2 : 0 ≤ c ^ 2 * Fintype.card V := by positivity
  nlinarith
