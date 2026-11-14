import AFTD.Prelude

/-!
# three_qubit_three_pairwise_zero_axes

Topic: quantum   Node: a0184ecacc25

Provenance: helper lemma.

For any three real 3 by 3 pair-correlation matrices there are unit axes for the three parties which simultaneously zero all three pair correlations.
-/

open Matrix Module

def three_qubit_three_pairwise_zero_axes_two_linear_forms
    (u w : Fin 3 → ℝ) : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun v := ![u ⬝ᵥ v, w ⬝ᵥ v]
  map_add' v1 v2 := by
    ext i
    fin_cases i <;> simp [dotProduct_add]
  map_smul' c v := by
    ext i
    fin_cases i <;> simp [dotProduct_smul]

lemma three_qubit_three_pairwise_zero_axes_exists_ne_zero_orthogonal (u w : Fin 3 → ℝ) :
    ∃ v : Fin 3 → ℝ, v ≠ 0 ∧ u ⬝ᵥ v = 0 ∧ w ⬝ᵥ v = 0 := by
  let f := three_qubit_three_pairwise_zero_axes_two_linear_forms u w
  have h_dim : finrank ℝ (Fin 3 → ℝ) = 3 := by rw [finrank_pi ℝ, Fintype.card_fin]
  have h_codim : finrank ℝ (Fin 2 → ℝ) = 2 := by rw [finrank_pi ℝ, Fintype.card_fin]
  have h_range_le : finrank ℝ f.range ≤ finrank ℝ (Fin 2 → ℝ) := Submodule.finrank_le f.range
  have h_sum := f.finrank_range_add_finrank_ker
  have h_ker_pos : 0 < finrank ℝ f.ker := by
    omega
  obtain ⟨⟨v, hv_mem⟩, hv_ne⟩ := finrank_pos_iff_exists_ne_zero.mp h_ker_pos
  refine ⟨v, ?_, ?_, ?_⟩
  · intro h
    apply hv_ne
    ext
    exact congr_fun h _
  · have h_zero : f v = 0 := LinearMap.mem_ker.mp hv_mem
    have h0 := congr_fun h_zero 0
    change (![u ⬝ᵥ v, w ⬝ᵥ v] : Fin 2 → ℝ) 0 = 0 at h0
    exact h0
  · have h_zero : f v = 0 := LinearMap.mem_ker.mp hv_mem
    have h1 := congr_fun h_zero 1
    change (![u ⬝ᵥ v, w ⬝ᵥ v] : Fin 2 → ℝ) 1 = 0 at h1
    exact h1

lemma three_qubit_three_pairwise_zero_axes_dotProduct_self_pos {v : Fin 3 → ℝ} (hv : v ≠ 0) : 0 < v ⬝ᵥ v := by
  have : (v ⬝ᵥ v) = ∑ i, (v i)^2 := by simp [dotProduct, sq]
  rw [this]
  apply Finset.sum_pos'
  · intro i _
    exact sq_nonneg (v i)
  · contrapose! hv
    ext i
    have := hv i (Finset.mem_univ i)
    exact sq_eq_zero_iff.mp (le_antisymm this (sq_nonneg (v i)))

lemma three_qubit_three_pairwise_zero_axes_normalize_dotProduct {v : Fin 3 → ℝ} (hv : v ≠ 0) :
    let c := (Real.sqrt (v ⬝ᵥ v))⁻¹ • v
    c ⬝ᵥ c = 1 := by
  intro c
  have hpos := three_qubit_three_pairwise_zero_axes_dotProduct_self_pos hv
  have hsq : (Real.sqrt (v ⬝ᵥ v)) ^ 2 = v ⬝ᵥ v := Real.sq_sqrt (le_of_lt hpos)
  dsimp [c]
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have h2 : (Real.sqrt (v ⬝ᵥ v))⁻¹ * ((Real.sqrt (v ⬝ᵥ v))⁻¹ * (v ⬝ᵥ v)) =
    ((Real.sqrt (v ⬝ᵥ v))⁻¹)^2 * (v ⬝ᵥ v) := by ring
  rw [h2, inv_pow, hsq]
  exact inv_mul_cancel₀ (ne_of_gt hpos)

lemma three_qubit_three_pairwise_zero_axes_dotProduct_smul_eq_zero {u v : Fin 3 → ℝ} (k : ℝ) (h : u ⬝ᵥ v = 0) :
    u ⬝ᵥ (k • v) = 0 := by
  rw [dotProduct_smul, smul_eq_mul, h, mul_zero]

lemma three_qubit_three_pairwise_zero_axes_exists_unit_orthogonal (u w : Fin 3 → ℝ) :
    ∃ c : Fin 3 → ℝ, (∑ i, (c i)^2) = 1 ∧ u ⬝ᵥ c = 0 ∧ w ⬝ᵥ c = 0 := by
  obtain ⟨v, hv, hu, hw⟩ := three_qubit_three_pairwise_zero_axes_exists_ne_zero_orthogonal u w
  let k := (Real.sqrt (v ⬝ᵥ v))⁻¹
  refine ⟨k • v, ?_, ?_, ?_⟩
  · have h1 := three_qubit_three_pairwise_zero_axes_normalize_dotProduct hv
    have h2 : (k • v) ⬝ᵥ (k • v) = ∑ i, ((k • v) i)^2 := by simp [dotProduct, sq]
    rw [← h2]
    exact h1
  · exact three_qubit_three_pairwise_zero_axes_dotProduct_smul_eq_zero k hu
  · exact three_qubit_three_pairwise_zero_axes_dotProduct_smul_eq_zero k hw

lemma three_qubit_three_pairwise_zero_axes_matrix_bilinear_eq (A : Matrix (Fin 3) (Fin 3) ℝ) (a b : Fin 3 → ℝ) :
    (∑ i, ∑ j, a i * A i j * b j) = (vecMul a A) ⬝ᵥ b := by
  simp only [vecMul, dotProduct]
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul, mul_assoc]

theorem three_qubit_three_pairwise_zero_axes (A B C : Matrix (Fin 3) (Fin 3) ℝ) :
    ∃ a b c : Fin 3 → ℝ,
      (∑ i, (a i)^2) = 1 ∧ (∑ i, (b i)^2) = 1 ∧ (∑ i, (c i)^2) = 1 ∧
      (∑ i, ∑ j, a i * A i j * b j) = 0 ∧
      (∑ i, ∑ j, a i * B i j * c j) = 0 ∧
      (∑ i, ∑ j, b i * C i j * c j) = 0 := by
  let a : Fin 3 → ℝ := ![(1 : ℝ), 0, 0]
  have ha : (∑ i, (a i)^2) = 1 := by simp [a, Fin.sum_univ_three]
  obtain ⟨b, hb, hab, -⟩ := three_qubit_three_pairwise_zero_axes_exists_unit_orthogonal (vecMul a A) 0
  obtain ⟨c, hc, hac, hbc⟩ := three_qubit_three_pairwise_zero_axes_exists_unit_orthogonal (vecMul a B) (vecMul b C)
  refine ⟨a, b, c, ha, hb, hc, ?_, ?_, ?_⟩
  · rw [three_qubit_three_pairwise_zero_axes_matrix_bilinear_eq]; exact hab
  · rw [three_qubit_three_pairwise_zero_axes_matrix_bilinear_eq]; exact hac
  · rw [three_qubit_three_pairwise_zero_axes_matrix_bilinear_eq]; exact hbc
