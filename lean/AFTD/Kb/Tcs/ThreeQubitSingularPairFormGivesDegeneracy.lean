import AFTD.Prelude
import AFTD.Kb.Tcs.ThreeQubitIsotropicPairFormGivesDegeneracy

/-!
# three_qubit_singular_pair_form_gives_degeneracy

Topic: quantum   Node: 7dc460afeb5f

Provenance: helper lemma.

If any of the three pair-correlation matrices is singular, the parallel-correlation hypothesis has unit-vector witnesses.
-/

lemma three_qubit_singular_pair_form_gives_degeneracy_exists_unit_mulVec_eq_zero
    (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : M.det = 0) :
    ∃ v : Fin 3 → ℝ, (∑ i, v i * v i) = 1 ∧ M.mulVec v = 0 := by
  have hdet : LinearMap.det (Matrix.toLin' M) = 0 := by
    rw [← LinearMap.det_toMatrix' (Matrix.toLin' M), LinearMap.toMatrix'_toLin', hM]
  have hker : (Matrix.toLin' M).ker ≠ ⊥ := LinearMap.det_eq_zero_iff_ker_ne_bot.mp hdet
  obtain ⟨v, hv_ker, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hv_eq : M.mulVec v = 0 := by
    rw [← Matrix.toLin'_apply]
    exact LinearMap.mem_ker.mp hv_ker
  let c := (Real.sqrt (v ⬝ᵥ v))⁻¹
  let u := c • v
  have hu_unit : (∑ i, u i * u i) = 1 :=
    three_qubit_isotropic_pair_form_gives_degeneracy_dotProduct_normalize hv_ne
  have hu_eq : M.mulVec u = 0 := by
    dsimp [u]
    rw [Matrix.mulVec_smul, hv_eq, smul_zero]
  exact ⟨u, hu_unit, hu_eq⟩

lemma three_qubit_singular_pair_form_gives_degeneracy_exists_unit_vecMul_eq_zero
    (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : M.det = 0) :
    ∃ v : Fin 3 → ℝ, (∑ i, v i * v i) = 1 ∧ Matrix.vecMul v M = 0 := by
  have hdet : M.transpose.det = 0 := by rw [Matrix.det_transpose, hM]
  obtain ⟨v, hv_unit, hv_eq⟩ :=
    three_qubit_singular_pair_form_gives_degeneracy_exists_unit_mulVec_eq_zero M.transpose hdet
  refine ⟨v, hv_unit, ?_⟩
  rw [← Matrix.mulVec_transpose]
  exact hv_eq

lemma three_qubit_singular_pair_form_gives_degeneracy_pair_zero_of_orth
    (A : Matrix (Fin 3) (Fin 3) ℝ) (a b : Fin 3 → ℝ)
    (h : (Matrix.mulVec A b) ⬝ᵥ a = 0) :
    (∑ i, ∑ j, a i * A i j * b j) = 0 := by
  rw [three_qubit_isotropic_pair_form_gives_degeneracy_pair_eq_dot,
      ← Matrix.dotProduct_mulVec,
      dotProduct_comm,
      h]

lemma three_qubit_singular_pair_form_gives_degeneracy_exists_r_n (u : Fin 3 → ℝ) :
    ∃ (n : Fin 3 → ℝ) (r : ℝ), (∑ i, n i * n i) = 1 ∧ (∀ j, u j = r * n j) := by
  by_cases hu : u = 0
  · refine ⟨![1, 0, 0], 0, ?_, ?_⟩
    · simp [Fin.sum_univ_three]
    · intro j
      rw [hu]
      simp
  · have hu_pos : 0 < u ⬝ᵥ u :=
      three_qubit_isotropic_pair_form_gives_degeneracy_dotProduct_pos_of_ne_zero hu
    have hu_sqrt_ne : Real.sqrt (u ⬝ᵥ u) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hu_pos)
    let cu := (Real.sqrt (u ⬝ᵥ u))⁻¹
    let n := cu • u
    let r := Real.sqrt (u ⬝ᵥ u)
    refine ⟨n, r, ?_, ?_⟩
    · exact three_qubit_isotropic_pair_form_gives_degeneracy_dotProduct_normalize hu
    · intro j
      dsimp [n, cu, r]
      rw [← mul_assoc, mul_inv_cancel₀ hu_sqrt_ne, one_mul]

lemma three_qubit_singular_pair_form_gives_degeneracy_q_zero_of_vecMul_A_zero
    (A B C : Matrix (Fin 3) (Fin 3) ℝ) (a : Fin 3 → ℝ)
    (ha : Matrix.vecMul a A = 0) :
    (let q := fun (a : Fin 3 → ℝ) =>
      ∑ i, ∑ j, ∑ k, ∑ l, a i * A i j * (C.transpose.adjugate) j k * B l k * a l
     q a = 0) := by
  dsimp
  rw [three_qubit_isotropic_pair_form_gives_degeneracy_q_eq_pair]
  rw [three_qubit_isotropic_pair_form_gives_degeneracy_pair_eq_dot]
  rw [ha, zero_dotProduct]

lemma three_qubit_singular_pair_form_gives_degeneracy_q_zero_of_vecMul_B_zero
    (A B C : Matrix (Fin 3) (Fin 3) ℝ) (a : Fin 3 → ℝ)
    (ha : Matrix.vecMul a B = 0) :
    (let q := fun (a : Fin 3 → ℝ) =>
      ∑ i, ∑ j, ∑ k, ∑ l, a i * A i j * (C.transpose.adjugate) j k * B l k * a l
     q a = 0) := by
  dsimp
  rw [three_qubit_isotropic_pair_form_gives_degeneracy_q_eq_pair]
  have hv : Matrix.mulVec C.transpose.adjugate (Matrix.vecMul a B) = 0 := by
    rw [ha, Matrix.mulVec_zero]
  rw [three_qubit_isotropic_pair_form_gives_degeneracy_pair_eq_dot]
  rw [hv, dotProduct_zero]

theorem three_qubit_singular_pair_form_gives_degeneracy
    (A B C : Matrix (Fin 3) (Fin 3) ℝ) :
    let dot := fun (a b : Fin 3 → ℝ) => ∑ i, a i * b i
    let pair := fun (M : Matrix (Fin 3) (Fin 3) ℝ) (a b : Fin 3 → ℝ) =>
      ∑ i, ∑ j, a i * M i j * b j
    (A.det = 0 ∨ B.det = 0 ∨ C.det = 0) →
    ∃ (a b n : Fin 3 → ℝ) (r s : ℝ),
      dot a a = 1 ∧ dot b b = 1 ∧ dot n n = 1 ∧ pair A a b = 0 ∧
      (∀ j, (∑ i, a i * B i j) = r * n j) ∧
      (∀ j, (∑ i, b i * C i j) = s * n j) := by
  intro dot pair h
  by_cases hC : C.det = 0
  · obtain ⟨b, hb_unit, hb_ker⟩ :=
      three_qubit_singular_pair_form_gives_degeneracy_exists_unit_vecMul_eq_zero C hC
    obtain ⟨a, ha_unit, ha_orth⟩ :=
      three_qubit_isotropic_pair_form_gives_degeneracy_exists_unit_orthogonal (Matrix.mulVec A b)
    have h_pair : pair A a b = 0 :=
      three_qubit_singular_pair_form_gives_degeneracy_pair_zero_of_orth A a b ha_orth
    let u := Matrix.vecMul a B
    obtain ⟨n, r, hn_unit, hr_eq⟩ :=
      three_qubit_singular_pair_form_gives_degeneracy_exists_r_n u
    refine ⟨a, b, n, r, 0, ha_unit, hb_unit, hn_unit, h_pair, ?_, ?_⟩
    · intro j
      have hu_def : (∑ i, a i * B i j) = u j := rfl
      rw [hu_def, hr_eq j]
    · intro j
      have hc_def : (∑ i, b i * C i j) = (Matrix.vecMul b C) j := rfl
      rw [hc_def, hb_ker]
      simp
  · have hAB : A.det = 0 ∨ B.det = 0 := by
      rcases h with hA | hB | hC_eq
      · exact Or.inl hA
      · exact Or.inr hB
      · exact False.elim (hC hC_eq)
    let q := fun (a : Fin 3 → ℝ) =>
      ∑ i, ∑ j, ∑ k, ∑ l, a i * A i j * (C.transpose.adjugate) j k * B l k * a l
    have hq : ∃ a : Fin 3 → ℝ, dot a a = 1 ∧ q a = 0 := by
      rcases hAB with hA | hB
      · obtain ⟨a, ha_unit, ha_ker⟩ :=
          three_qubit_singular_pair_form_gives_degeneracy_exists_unit_vecMul_eq_zero A hA
        exact ⟨a, ha_unit,
          three_qubit_singular_pair_form_gives_degeneracy_q_zero_of_vecMul_A_zero A B C a ha_ker⟩
      · obtain ⟨a, ha_unit, ha_ker⟩ :=
          three_qubit_singular_pair_form_gives_degeneracy_exists_unit_vecMul_eq_zero B hB
        exact ⟨a, ha_unit,
          three_qubit_singular_pair_form_gives_degeneracy_q_zero_of_vecMul_B_zero A B C a ha_ker⟩
    exact three_qubit_isotropic_pair_form_gives_degeneracy A B C hC hq
