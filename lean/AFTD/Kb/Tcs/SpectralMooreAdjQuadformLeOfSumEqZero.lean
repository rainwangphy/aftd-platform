import AFTD.Prelude
import AFTD.Kb.Tcs.SpectralMooreSecondEigenvalueLe
import AFTD.Kb.Physics.IsSymmetric

/-!
# spectral_moore_adj_quadform_le_of_sum_eq_zero

Topic: graphs   Node: 44e87332cfb6

Provenance: helper lemma. arXiv:2611.00591 (A spectral Moore problem and the Yang-Koolen conjecture), Section 5, the positive semidefiniteness of M = I + αS_G in (11)

For a k-regular finite simple graph G on a vertex type V whose second largest adjacency eigenvalue is at most θ (spectral_moore_second_eigenvalue_le G θ), every real vector z : V → ℝ with coordinate sum zero satisfies z ⬝ᵥ (G.adjMatrix ℝ *ᵥ z) ≤ θ * (z ⬝ᵥ z).
-/

lemma spectral_moore_adj_quadform_aux_qf
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {N : ℕ} (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) (hN : Module.finrank ℝ E = N)
    (j0 : Fin N) (c : ℝ) (hc : ∀ k, k ≠ j0 → hT.eigenvalues hN k ≤ c)
    (v : E) (hv : inner ℝ (hT.eigenvectorBasis hN j0) v = 0) :
    inner ℝ (T v) v ≤ c * inner ℝ v v := by
  have qform : inner ℝ (T v) v = ∑ i : Fin N, hT.eigenvalues hN i * (inner ℝ (hT.eigenvectorBasis hN i) v)^2 := by
    rw [← OrthonormalBasis.sum_inner_mul_inner (hT.eigenvectorBasis hN) (T v) v]
    apply Finset.sum_congr rfl
    intro i _
    rw [hT v (hT.eigenvectorBasis hN i), hT.apply_eigenvectorBasis hN i, inner_smul_right]
    simp only [RCLike.ofReal_real_eq_id, id_eq]
    rw [real_inner_comm v]
    ring
  have pars : inner ℝ v v = ∑ i : Fin N, (inner ℝ (hT.eigenvectorBasis hN i) v)^2 := by
    rw [← OrthonormalBasis.sum_inner_mul_inner (hT.eigenvectorBasis hN) v v]
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_comm v]
    ring
  rw [qform, pars, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : k = j0
  · subst hk; rw [hv]; simp
  · exact mul_le_mul_of_nonneg_right (hc k hk) (sq_nonneg _)

open Classical SimpleGraph Matrix in
lemma spectral_moore_adj_quadform_aux_deg {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ)
    (hreg : G.IsRegularOfDegree k) (x : V → ℝ) :
    x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) ≤ k * (x ⬝ᵥ x) := by
  have h := (G.posSemidef_lapMatrix ℝ).dotProduct_mulVec_nonneg x
  simp only [star_trivial, lapMatrix, sub_mulVec, dotProduct_sub,
    dotProduct_mulVec_degMatrix] at h
  have : ∑ i : V, (G.degree i : ℝ) * x i * x i = k * (x ⬝ᵥ x) := by
    simp only [dotProduct, Finset.mul_sum, hreg.degree_eq]
    exact Finset.sum_congr rfl fun i _ => by ring
  linarith

open Classical SimpleGraph Matrix in
theorem spectral_moore_adj_quadform_le_of_sum_eq_zero {V : Type*} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) (θ : ℝ) (hreg : G.IsRegularOfDegree k)
    (hθ : spectral_moore_second_eigenvalue_le G θ) (z : V → ℝ) (hz : ∑ v, z v = 0) :
    z ⬝ᵥ (G.adjMatrix ℝ *ᵥ z) ≤ θ * (z ⬝ᵥ z) := by
  set A := G.adjMatrix ℝ with hA
  have hdeg := spectral_moore_adj_quadform_aux_deg G k hreg
  have hsymm : A.toEuclideanLin.IsSymmetric :=
    isSymmetric_toEuclideanLin_iff.mpr (G.isHermitian_adjMatrix ℝ)
  have h1 : A *ᵥ (fun _ : V => (1 : ℝ)) = fun _ => (k : ℝ) := by
    funext v
    simp only [A, adjMatrix_mulVec_apply, Finset.sum_const, card_neighborFinset_eq_degree,
      hreg.degree_eq, nsmul_eq_mul, mul_one]
  have hAsymm : ∀ x y : V → ℝ, x ⬝ᵥ (A *ᵥ y) = (A *ᵥ x) ⬝ᵥ y := by
    intro x y
    rw [dotProduct_mulVec, ← mulVec_transpose, (G.isSymm_adjMatrix (α := ℝ)).eq, dotProduct_comm]
  have one_A_z : (fun _ : V => (1 : ℝ)) ⬝ᵥ (A *ᵥ z) = 0 := by
    rw [hAsymm, h1]; simp [dotProduct, ← Finset.mul_sum, hz]
  have one_A_one : (fun _ : V => (1 : ℝ)) ⬝ᵥ (A *ᵥ (fun _ : V => (1 : ℝ))) = k * Fintype.card V := by
    rw [h1]; simp [dotProduct, mul_comm]
  have one_one : (fun _ : V => (1 : ℝ)) ⬝ᵥ (fun _ : V => (1 : ℝ)) = Fintype.card V := by
    simp only [dotProduct, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have z_one : z ⬝ᵥ (fun _ : V => (1 : ℝ)) = 0 := by simp [dotProduct, hz]
  by_cases hkθ : (k : ℝ) ≤ θ
  · have := hdeg z
    have hzz : 0 ≤ z ⬝ᵥ z := by
      simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    nlinarith
  rw [not_le] at hkθ
  rcases Nat.eq_zero_or_pos (Fintype.card V) with hn | hn
  · have : IsEmpty V := Fintype.card_eq_zero_iff.mp hn
    simp [dotProduct]
  -- the Rayleigh bound on the complement of the top eigenvector
  have e1 : ∀ u w : V → ℝ, inner ℝ (WithLp.toLp 2 u) (WithLp.toLp 2 w) = u ⬝ᵥ w := by
    intro u w; rw [EuclideanSpace.inner_eq_star_dotProduct]; simp [dotProduct_comm]
  set b := hsymm.eigenvectorBasis finrank_euclideanSpace ⟨0, by simpa [finrank_euclideanSpace] using hn⟩ with hb
  have key : ∀ y : V → ℝ, inner ℝ b (WithLp.toLp 2 y) = 0 →
      y ⬝ᵥ (A *ᵥ y) ≤ θ * (y ⬝ᵥ y) := by
    intro y hy
    have := spectral_moore_adj_quadform_aux_qf A.toEuclideanLin hsymm finrank_euclideanSpace _ θ
      (fun i hi => hθ i (by
        rcases i with ⟨i, hi'⟩
        simp only [ne_eq, Fin.mk.injEq] at hi
        simp only; omega)) _ hy
    rw [show A.toEuclideanLin (WithLp.toLp 2 y) = WithLp.toLp 2 (A *ᵥ y) from rfl, e1, e1] at this
    rwa [dotProduct_comm]
  set one : V → ℝ := fun _ => 1 with hone
  have hn' : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  by_cases hγ : inner ℝ b (WithLp.toLp 2 one) = 0
  · have := key one hγ
    rw [one_A_one, one_one] at this
    nlinarith
  set β := inner ℝ b (WithLp.toLp 2 z) / inner ℝ b (WithLp.toLp 2 one) with hβ
  have hy : inner ℝ b (WithLp.toLp 2 (z - β • one)) = 0 := by
    rw [WithLp.toLp_sub, WithLp.toLp_smul, inner_sub_right, inner_smul_right, hβ]
    field_simp; ring
  have := key _ hy
  have exp1 : (z - β • one) ⬝ᵥ (A *ᵥ (z - β • one)) =
      z ⬝ᵥ (A *ᵥ z) - 2 * β * (one ⬝ᵥ (A *ᵥ z)) + β ^ 2 * (one ⬝ᵥ (A *ᵥ one)) := by
    have hs : one ⬝ᵥ (A *ᵥ z) = z ⬝ᵥ (A *ᵥ one) := by rw [hAsymm, dotProduct_comm]
    simp only [mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, hs]
    ring
  have exp2 : (z - β • one) ⬝ᵥ (z - β • one) = z ⬝ᵥ z + β ^ 2 * (one ⬝ᵥ one) := by
    have hs : one ⬝ᵥ z = 0 := by rw [dotProduct_comm]; exact z_one
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul, hs,
      z_one]
    ring
  rw [exp1, exp2, one_A_z, one_A_one, one_one] at this
  have hβ2 : 0 ≤ β ^ 2 * Fintype.card V := by positivity
  nlinarith
