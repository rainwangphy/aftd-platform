import AFTD.Prelude

/-!
# three_qubit_isotropic_pair_form_gives_degeneracy

Topic: quantum   Node: 049185ad19ee

Provenance: helper lemma.

For invertible third-pair correlation matrix C, a nonzero isotropic vector of the displayed adjugate quadratic form gives a pair-orthogonal unit pair whose remaining two correlation vectors are parallel.
-/

open Matrix

lemma three_qubit_isotropic_pair_form_gives_degeneracy_dotProduct_pos_of_ne_zero
    {n : Type*} [Fintype n] {v : n → ℝ} (hv : v ≠ 0) : 0 < v ⬝ᵥ v := by
  have h1 : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
  have h2 : v ⬝ᵥ v ≠ 0 := by
    intro h
    exact hv (dotProduct_self_eq_zero.mp h)
  exact lt_of_le_of_ne h1 h2.symm

lemma three_qubit_isotropic_pair_form_gives_degeneracy_dotProduct_smul_smul
    {n : Type*} [Fintype n] (c d : ℝ) (v w : n → ℝ) :
    (c • v) ⬝ᵥ (d • w) = c * d * (v ⬝ᵥ w) := by
  simp_rw [dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma three_qubit_isotropic_pair_form_gives_degeneracy_dotProduct_smul_right
    {n : Type*} [Fintype n] (c : ℝ) (v w : n → ℝ) :
    v ⬝ᵥ (c • w) = c * (v ⬝ᵥ w) := by
  simp_rw [dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma three_qubit_isotropic_pair_form_gives_degeneracy_dotProduct_normalize
    {n : Type*} [Fintype n] {v : n → ℝ} (hv : v ≠ 0) :
    let c := (Real.sqrt (v ⬝ᵥ v))⁻¹
    (c • v) ⬝ᵥ (c • v) = 1 := by
  intro c
  have hpos : 0 < v ⬝ᵥ v := three_qubit_isotropic_pair_form_gives_degeneracy_dotProduct_pos_of_ne_zero hv
  rw [three_qubit_isotropic_pair_form_gives_degeneracy_dotProduct_smul_smul]
  dsimp [c]
  have hsq : (Real.sqrt (v ⬝ᵥ v)) ^ 2 = v ⬝ᵥ v := Real.sq_sqrt (le_of_lt hpos)
  have : (Real.sqrt (v ⬝ᵥ v))⁻¹ * (Real.sqrt (v ⬝ᵥ v))⁻¹ * (v ⬝ᵥ v) = 1 := by
    rw [← mul_inv, ← sq, hsq, inv_mul_cancel₀ (ne_of_gt hpos)]
  exact this

lemma three_qubit_isotropic_pair_form_gives_degeneracy_pair_smul_right
    (M : Matrix (Fin 3) (Fin 3) ℝ) (a v : Fin 3 → ℝ) (c : ℝ) :
    (∑ i, ∑ j, a i * M i j * (c • v) j) = c * ∑ i, ∑ j, a i * M i j * v j := by
  simp_rw [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  repeat (apply Finset.sum_congr rfl; intros _ _)
  ring

lemma three_qubit_isotropic_pair_form_gives_degeneracy_pair_eq_dot
    (M : Matrix (Fin 3) (Fin 3) ℝ) (a b : Fin 3 → ℝ) :
    (∑ i, ∑ j, a i * M i j * b j) = (vecMul a M) ⬝ᵥ b := by
  have : (∑ i, ∑ j, a i * M i j * b j) = a ⬝ᵥ (M *ᵥ b) := by
    rw [dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    rw [mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [this, dotProduct_mulVec]

lemma three_qubit_isotropic_pair_form_gives_degeneracy_q_eq_pair
    (A B C : Matrix (Fin 3) (Fin 3) ℝ) (a : Fin 3 → ℝ) :
    let v := C.transpose.adjugate *ᵥ (vecMul a B)
    (∑ i, ∑ j, ∑ k, ∑ l, a i * A i j * (C.transpose.adjugate) j k * B l k * a l) =
      ∑ i, ∑ j, a i * A i j * v j := by
  intro v
  change (∑ i, ∑ j, ∑ k, ∑ l, a i * A i j * (C.transpose.adjugate) j k * B l k * a l) =
    ∑ i, ∑ j, a i * A i j * (C.transpose.adjugate *ᵥ (vecMul a B)) j
  unfold mulVec vecMul dotProduct
  simp_rw [Finset.mul_sum]
  repeat (apply Finset.sum_congr rfl; intros _ _)
  ring

lemma three_qubit_isotropic_pair_form_gives_degeneracy_vecMul_adj_transpose
    (C : Matrix (Fin 3) (Fin 3) ℝ) (u : Fin 3 → ℝ) :
    vecMul (C.transpose.adjugate *ᵥ u) C = C.det • u := by
  rw [← mulVec_transpose, mulVec_mulVec, mul_adjugate, smul_mulVec, one_mulVec, det_transpose]

lemma three_qubit_isotropic_pair_form_gives_degeneracy_vecMul_ne_zero_of_det_ne_zero
    (C : Matrix (Fin 3) (Fin 3) ℝ) (hC : C.det ≠ 0)
    (b : Fin 3 → ℝ) (hb : b ≠ 0) : vecMul b C ≠ 0 := by
  intro hz
  have h1 : vecMul (vecMul b C) C.adjugate = 0 := by rw [hz, zero_vecMul]
  rw [vecMul_vecMul, mul_adjugate, vecMul_smul, vecMul_one] at h1
  have h2 : C.det • b = 0 := h1
  have h3 : b = 0 := by
    ext i
    have := congr_fun h2 i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    exact mul_eq_zero.mp this |>.resolve_left hC
  exact hb h3

lemma three_qubit_isotropic_pair_form_gives_degeneracy_ne_zero_of_dot_self_one
    {n : Type*} [Fintype n] {b : n → ℝ} (hb : b ⬝ᵥ b = 1) : b ≠ 0 := by
  intro h
  subst h
  rw [dotProduct_zero] at hb
  exact zero_ne_one hb

lemma three_qubit_isotropic_pair_form_gives_degeneracy_u_eq_zero_of_v_eq_zero
    (C : Matrix (Fin 3) (Fin 3) ℝ) (hC : C.det ≠ 0) (u : Fin 3 → ℝ)
    (hv : C.transpose.adjugate *ᵥ u = 0) : u = 0 := by
  have h1 : vecMul (C.transpose.adjugate *ᵥ u) C = 0 := by rw [hv, zero_vecMul]
  have h2 := three_qubit_isotropic_pair_form_gives_degeneracy_vecMul_adj_transpose C u
  rw [h2] at h1
  ext i
  have := congr_fun h1 i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
  exact mul_eq_zero.mp this |>.resolve_left hC

lemma three_qubit_isotropic_pair_form_gives_degeneracy_u_ne_zero_of_v_ne_zero
    (C : Matrix (Fin 3) (Fin 3) ℝ) (u : Fin 3 → ℝ)
    (hv : C.transpose.adjugate *ᵥ u ≠ 0) : u ≠ 0 := by
  intro hu
  subst hu
  rw [mulVec_zero] at hv
  exact hv rfl

lemma three_qubit_isotropic_pair_form_gives_degeneracy_exists_unit_orthogonal
    (w : Fin 3 → ℝ) : ∃ b : Fin 3 → ℝ, (b ⬝ᵥ b = 1) ∧ (w ⬝ᵥ b = 0) := by
  by_cases h : w 0 = 0 ∧ w 1 = 0
  · refine ⟨![1, 0, 0], ?_, ?_⟩
    · rw [dotProduct, Fin.sum_univ_three]; dsimp; ring
    · rw [dotProduct, Fin.sum_univ_three]; dsimp; rw [h.1, h.2]; ring
  · have hne : ![-w 1, w 0, 0] ≠ 0 := by
      intro h0
      have : ![-w 1, w 0, 0] 0 = 0 := by rw [h0]; rfl
      have : ![-w 1, w 0, 0] 1 = 0 := by rw [h0]; rfl
      dsimp at *
      have hw1 : w 1 = 0 := by linarith
      have hw0 : w 0 = 0 := by linarith
      exact h ⟨hw0, hw1⟩
    let v : Fin 3 → ℝ := ![-w 1, w 0, 0]
    let c := (Real.sqrt (v ⬝ᵥ v))⁻¹
    refine ⟨c • v, three_qubit_isotropic_pair_form_gives_degeneracy_dotProduct_normalize hne, ?_⟩
    rw [three_qubit_isotropic_pair_form_gives_degeneracy_dotProduct_smul_right]
    have : w ⬝ᵥ v = 0 := by
      rw [dotProduct, Fin.sum_univ_three]; dsimp [v]; ring
    rw [this, mul_zero]

theorem three_qubit_isotropic_pair_form_gives_degeneracy
    (A B C : Matrix (Fin 3) (Fin 3) ℝ) (hC : C.det ≠ 0) :
    let dot := fun (a b : Fin 3 → ℝ) => ∑ i, a i * b i
    let pair := fun (M : Matrix (Fin 3) (Fin 3) ℝ) (a b : Fin 3 → ℝ) =>
      ∑ i, ∑ j, a i * M i j * b j
    let q := fun (a : Fin 3 → ℝ) =>
      ∑ i, ∑ j, ∑ k, ∑ l, a i * A i j * (C.transpose.adjugate) j k * B l k * a l
    (∃ a : Fin 3 → ℝ, dot a a = 1 ∧ q a = 0) →
    ∃ (a b n : Fin 3 → ℝ) (r s : ℝ),
      dot a a = 1 ∧ dot b b = 1 ∧ dot n n = 1 ∧ pair A a b = 0 ∧
      (∀ j, (∑ i, a i * B i j) = r * n j) ∧
      (∀ j, (∑ i, b i * C i j) = s * n j) := by
  intro dot pair q ⟨a, ha_unit, ha_q⟩
  let u : Fin 3 → ℝ := vecMul a B
  let v : Fin 3 → ℝ := C.transpose.adjugate *ᵥ u
  have hq_pair : q a = pair A a v := three_qubit_isotropic_pair_form_gives_degeneracy_q_eq_pair A B C a
  have h_pair_v : pair A a v = 0 := by rw [← hq_pair, ha_q]
  by_cases hv : v = 0
  · have hu : u = 0 := three_qubit_isotropic_pair_form_gives_degeneracy_u_eq_zero_of_v_eq_zero C hC u hv
    let w : Fin 3 → ℝ := vecMul a A
    obtain ⟨b, hb_unit, hb_orth⟩ := three_qubit_isotropic_pair_form_gives_degeneracy_exists_unit_orthogonal w
    have hb_ne : b ≠ 0 := three_qubit_isotropic_pair_form_gives_degeneracy_ne_zero_of_dot_self_one hb_unit
    let z : Fin 3 → ℝ := vecMul b C
    have hz_ne : z ≠ 0 := three_qubit_isotropic_pair_form_gives_degeneracy_vecMul_ne_zero_of_det_ne_zero C hC b hb_ne
    let cz := (Real.sqrt (z ⬝ᵥ z))⁻¹
    let n := cz • z
    have hn_unit : dot n n = 1 := three_qubit_isotropic_pair_form_gives_degeneracy_dotProduct_normalize hz_ne
    have h_pair_b : pair A a b = 0 := by
      have := three_qubit_isotropic_pair_form_gives_degeneracy_pair_eq_dot A a b
      exact this.trans hb_orth
    have hz_pos : 0 < z ⬝ᵥ z := three_qubit_isotropic_pair_form_gives_degeneracy_dotProduct_pos_of_ne_zero hz_ne
    have hz_sqrt_ne : Real.sqrt (z ⬝ᵥ z) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hz_pos)
    refine ⟨a, b, n, 0, Real.sqrt (z ⬝ᵥ z), ha_unit, hb_unit, hn_unit, h_pair_b, ?_, ?_⟩
    · intro j
      have hu_j : u j = 0 := congr_fun hu j
      have hu_def : (∑ i, a i * B i j) = u j := rfl
      rw [hu_def, hu_j, zero_mul]
    · intro j
      have h1 : (∑ i, b i * C i j) = z j := rfl
      rw [h1]
      dsimp [n, cz]
      rw [← mul_assoc, mul_inv_cancel₀ hz_sqrt_ne, one_mul]
  · have hu : u ≠ 0 := three_qubit_isotropic_pair_form_gives_degeneracy_u_ne_zero_of_v_ne_zero C u hv
    let cv := (Real.sqrt (v ⬝ᵥ v))⁻¹
    let cu := (Real.sqrt (u ⬝ᵥ u))⁻¹
    let b := cv • v
    let n := cu • u
    let r := Real.sqrt (u ⬝ᵥ u)
    let s := cv * C.det * r
    have hb_unit : dot b b = 1 := three_qubit_isotropic_pair_form_gives_degeneracy_dotProduct_normalize hv
    have hn_unit : dot n n = 1 := three_qubit_isotropic_pair_form_gives_degeneracy_dotProduct_normalize hu
    have h_pair_b : pair A a b = 0 := by
      have h_pair_v' : (∑ i, ∑ j, a i * A i j * v j) = 0 := h_pair_v
      change (∑ i, ∑ j, a i * A i j * (cv • v) j) = 0
      rw [three_qubit_isotropic_pair_form_gives_degeneracy_pair_smul_right, h_pair_v', mul_zero]
    have hu_pos : 0 < u ⬝ᵥ u := three_qubit_isotropic_pair_form_gives_degeneracy_dotProduct_pos_of_ne_zero hu
    have hu_sqrt_ne : Real.sqrt (u ⬝ᵥ u) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hu_pos)
    have h_vecMul_v : vecMul v C = C.det • u :=
      three_qubit_isotropic_pair_form_gives_degeneracy_vecMul_adj_transpose C u
    refine ⟨a, b, n, r, s, ha_unit, hb_unit, hn_unit, h_pair_b, ?_, ?_⟩
    · intro j
      have hu_def : (∑ i, a i * B i j) = u j := rfl
      rw [hu_def]
      dsimp [n, cu, r]
      rw [← mul_assoc, mul_inv_cancel₀ hu_sqrt_ne, one_mul]
    · intro j
      have h1 : (∑ i, b i * C i j) = (vecMul b C) j := rfl
      rw [h1]
      dsimp [b]
      rw [smul_vecMul, h_vecMul_v, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
      dsimp [s, n, cu, r]
      rw [mul_assoc (cv * C.det), ← mul_assoc (Real.sqrt (u ⬝ᵥ u)), mul_inv_cancel₀ hu_sqrt_ne, one_mul, mul_assoc]
