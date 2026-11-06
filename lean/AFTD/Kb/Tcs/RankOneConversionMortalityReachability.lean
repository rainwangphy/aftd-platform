import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixIsMortal
import AFTD.Kb.Tcs.MatrixRankOneSandwichIdentity

/-!
# rank_one_conversion_mortality_reachability

Topic: computability   Node: fc1251ba4ee9

Provenance: formalization of a published result. Source: arXiv:2611.06562 Lemma 3.1

Let 𝒢 be a finite set of invertible 2 × 2 rational matrices, and let s, t be one-dimensional linear subspaces of ℚ². Let u be a nonzero integer column vector spanning s, and let λ be a nonzero integer row vector with kernel t. Set R = u λ. Then 𝒢 ∪ {R} is mortal if and only if there exists a word W in 𝒢* such that W(s) = t.
-/

open Matrix

lemma rank_one_conversion_list_split_first {α : Type*} [DecidableEq α] (x : α) (l : List α) (hx : x ∈ l) :
    ∃ as bs, l = as ++ x :: bs ∧ x ∉ as := by
  induction l with
  | nil => contradiction
  | cons y ys ih =>
    by_cases hy : y = x
    · subst hy
      exact ⟨[], ys, rfl, by simp⟩
    · obtain ⟨as, bs, h1, h2⟩ := ih (by aesop)
      refine ⟨y :: as, bs, by simp [h1], ?_⟩
      simp [Ne.symm hy, h2]

lemma rank_one_conversion_span_eq_of_dot_eq_zero (lam v w : Fin 2 → ℚ) (hlam : lam ≠ 0) (hw : w ≠ 0)
    (hv : lam ⬝ᵥ v = 0) (hw0 : lam ⬝ᵥ w = 0) :
    v ∈ Submodule.span ℚ {w} := by
  have hdot (x y : Fin 2 → ℚ) : x ⬝ᵥ y = x 0 * y 0 + x 1 * y 1 := by
    simp [dotProduct, Fin.sum_univ_two]
  rw [hdot] at hv hw0
  have hdet : w 0 * v 1 - w 1 * v 0 = 0 := by
    have h1 : lam 0 * (w 0 * v 1 - w 1 * v 0) = 0 := by
      calc lam 0 * (w 0 * v 1 - w 1 * v 0)
        _ = (lam 0 * w 0 + lam 1 * w 1) * v 1 - w 1 * (lam 0 * v 0 + lam 1 * v 1) := by ring
        _ = 0 * v 1 - w 1 * 0 := by rw [hw0, hv]
        _ = 0 := by ring
    have h2 : lam 1 * (w 0 * v 1 - w 1 * v 0) = 0 := by
      calc lam 1 * (w 0 * v 1 - w 1 * v 0)
        _ = w 0 * (lam 0 * v 0 + lam 1 * v 1) - (lam 0 * w 0 + lam 1 * w 1) * v 0 := by ring
        _ = w 0 * 0 - 0 * v 0 := by rw [hv, hw0]
        _ = 0 := by ring
    have : lam 0 = 0 ∧ lam 1 = 0 → False := by
      intro ⟨a, b⟩
      apply hlam
      ext i; fin_cases i <;> assumption
    by_cases h0 : lam 0 = 0
    · have h1' : lam 1 ≠ 0 := fun h => this ⟨h0, h⟩
      exact mul_eq_zero.mp h2 |>.resolve_left h1'
    · exact mul_eq_zero.mp h1 |>.resolve_left h0
  rw [Submodule.mem_span_singleton]
  have hw_cases : w 0 ≠ 0 ∨ w 1 ≠ 0 := by
    contrapose! hw
    ext i; fin_cases i <;> aesop
  rcases hw_cases with hw0_ne | hw1_ne
  · use v 0 / w 0
    ext i
    fin_cases i
    · simp; exact div_mul_cancel₀ (v 0) hw0_ne
    · simp
      have : w 0 * v 1 = w 1 * v 0 := by linarith [hdet]
      calc v 0 / w 0 * w 1 = (w 1 * v 0) / w 0 := by ring
      _ = (w 0 * v 1) / w 0 := by rw [this]
      _ = v 1 := mul_div_cancel_left₀ (v 1) hw0_ne
  · use v 1 / w 1
    ext i
    fin_cases i
    · simp
      have : w 1 * v 0 = w 0 * v 1 := by linarith [hdet]
      calc v 1 / w 1 * w 0 = (w 0 * v 1) / w 1 := by ring
      _ = (w 1 * v 0) / w 1 := by rw [this]
      _ = v 0 := mul_div_cancel_left₀ (v 0) hw1_ne
    · simp; exact div_mul_cancel₀ (v 1) hw1_ne

lemma rank_one_conversion_span_eq_t_of_dot_zero (lam w : Fin 2 → ℚ) (hlam : lam ≠ 0) (hw : w ≠ 0)
    (t : Submodule ℚ (Fin 2 → ℚ))
    (ht : ∀ v : Fin 2 → ℚ, v ∈ t ↔ lam ⬝ᵥ v = 0)
    (hw0 : lam ⬝ᵥ w = 0) :
    Submodule.span ℚ {w} = t := by
  apply le_antisymm
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact (ht w).2 hw0
  · intro v hv
    exact rank_one_conversion_span_eq_of_dot_eq_zero lam v w hlam hw ((ht v).1 hv) hw0

lemma rank_one_conversion_R_ne_zero (u lam : Fin 2 → ℤ) (hu : u ≠ 0) (hlam : lam ≠ 0) :
    vecMulVec (algebraMap ℤ ℚ ∘ u) (algebraMap ℤ ℚ ∘ lam) ≠ 0 := by
  have hu_cases : u 0 ≠ 0 ∨ u 1 ≠ 0 := by
    contrapose! hu; ext i; fin_cases i <;> aesop
  have hlam_cases : lam 0 ≠ 0 ∨ lam 1 ≠ 0 := by
    contrapose! hlam; ext i; fin_cases i <;> aesop
  intro h
  have hij (i j : Fin 2) : (algebraMap ℤ ℚ ∘ u) i * (algebraMap ℤ ℚ ∘ lam) j = 0 := by
    have : (vecMulVec (algebraMap ℤ ℚ ∘ u) (algebraMap ℤ ℚ ∘ lam)) i j = 0 := by rw [h]; rfl
    simpa [vecMulVec] using this
  rcases hu_cases with hu0 | hu1 <;> rcases hlam_cases with hl0 | hl1
  · have := hij 0 0; simp only [Function.comp_apply] at this
    cases mul_eq_zero.mp this with
    | inl h => exact hu0 (Int.cast_eq_zero.mp h)
    | inr h => exact hl0 (Int.cast_eq_zero.mp h)
  · have := hij 0 1; simp only [Function.comp_apply] at this
    cases mul_eq_zero.mp this with
    | inl h => exact hu0 (Int.cast_eq_zero.mp h)
    | inr h => exact hl1 (Int.cast_eq_zero.mp h)
  · have := hij 1 0; simp only [Function.comp_apply] at this
    cases mul_eq_zero.mp this with
    | inl h => exact hu1 (Int.cast_eq_zero.mp h)
    | inr h => exact hl0 (Int.cast_eq_zero.mp h)
  · have := hij 1 1; simp only [Function.comp_apply] at this
    cases mul_eq_zero.mp this with
    | inl h => exact hu1 (Int.cast_eq_zero.mp h)
    | inr h => exact hl1 (Int.cast_eq_zero.mp h)

/-- Rank-one conversion between projective reachability and matrix mortality (arXiv:2611.06562 Lemma 3.1). -/
theorem rank_one_conversion_mortality_reachability (𝒢 : Set (Matrix (Fin 2) (Fin 2) ℚ)) (h𝒢_fin : 𝒢.Finite) (h𝒢_inv : ∀ M ∈ 𝒢, IsUnit M) (u lam : Fin 2 → ℤ) (hu : u ≠ 0) (hlam : lam ≠ 0) (s t : Submodule ℚ (Fin 2 → ℚ)) (hs : s = Submodule.span ℚ {algebraMap ℤ ℚ ∘ u}) (ht : ∀ v : Fin 2 → ℚ, v ∈ t ↔ (algebraMap ℤ ℚ ∘ lam) ⬝ᵥ v = 0) (R : Matrix (Fin 2) (Fin 2) ℤ) (hR : R = Matrix.vecMulVec u lam) : matrix_is_mortal (𝒢 ∪ {R.map (algebraMap ℤ ℚ)}) ↔ ∃ W : List (Matrix (Fin 2) (Fin 2) ℚ), (∀ M ∈ W, M ∈ 𝒢) ∧ Submodule.map (Matrix.toLin' W.prod) s = t := by
  set u_Q : Fin 2 → ℚ := algebraMap ℤ ℚ ∘ u
  set lam_Q : Fin 2 → ℚ := algebraMap ℤ ℚ ∘ lam
  set R_Q : Matrix (Fin 2) (Fin 2) ℚ := R.map (algebraMap ℤ ℚ)
  have hR_Q : R_Q = vecMulVec u_Q lam_Q := by
    ext i j; simp [hR, vecMulVec, R_Q, u_Q, lam_Q]
  have hu_Q : u_Q ≠ 0 := by
    intro h; apply hu; ext i
    have : u_Q i = (0 : Fin 2 → ℚ) i := by rw [h]
    exact Int.cast_eq_zero.mp this
  have hlam_Q : lam_Q ≠ 0 := by
    intro h; apply hlam; ext i
    have : lam_Q i = (0 : Fin 2 → ℚ) i := by rw [h]
    exact Int.cast_eq_zero.mp this
  have hR_ne : R_Q ≠ 0 := by
    rw [hR_Q]
    exact rank_one_conversion_R_ne_zero u lam hu hlam
  have hmap_eq (W : List (Matrix (Fin 2) (Fin 2) ℚ)) (hW : ∀ M ∈ W, M ∈ 𝒢) :
      Submodule.map (Matrix.toLin' W.prod) s = t ↔ lam_Q ⬝ᵥ (W.prod *ᵥ u_Q) = 0 := by
    have hW_unit : IsUnit W.prod := List.prod_isUnit (fun M hM => h𝒢_inv M (hW M hM))
    have hWu_ne : W.prod *ᵥ u_Q ≠ 0 := by
      intro h
      obtain ⟨unit, hu_prod⟩ := hW_unit
      have : (↑unit⁻¹ : Matrix (Fin 2) (Fin 2) ℚ) *ᵥ (↑unit *ᵥ u_Q) = 0 := by
        rw [hu_prod, h, mulVec_zero]
      rw [mulVec_mulVec, Units.inv_mul, one_mulVec] at this
      exact hu_Q this
    have hmap : Submodule.map (Matrix.toLin' W.prod) s = Submodule.span ℚ {W.prod *ᵥ u_Q} := by
      rw [hs, Submodule.map_span, Set.image_singleton, toLin'_apply]
    constructor
    · intro h
      rw [hmap] at h
      have : W.prod *ᵥ u_Q ∈ Submodule.span ℚ {W.prod *ᵥ u_Q} := Submodule.mem_span_singleton_self _
      rw [h, ht] at this
      exact this
    · intro h
      rw [hmap]
      exact rank_one_conversion_span_eq_t_of_dot_zero lam_Q _ hlam_Q hWu_ne t ht h
  constructor
  · rintro ⟨L, hL_ne, hL_mem, hL_prod⟩
    have h_ind : ∀ (L : List (Matrix (Fin 2) (Fin 2) ℚ)),
        L ≠ [] → (∀ M ∈ L, M ∈ 𝒢 ∪ {R_Q}) → L.prod = 0 →
        ∃ W : List (Matrix (Fin 2) (Fin 2) ℚ), (∀ M ∈ W, M ∈ 𝒢) ∧ Submodule.map (Matrix.toLin' W.prod) s = t := by
      intro L
      induction hn : L.length using Nat.strong_induction_on generalizing L with
      | h n ih =>
        intro hne hmem hprod
        subst hn
        cases L with
        | nil => contradiction
        | cons M L' =>
          by_cases hM : M ∈ 𝒢
          · have hM_unit : IsUnit M := h𝒢_inv M hM
            have hL'_prod : L'.prod = 0 := by
              obtain ⟨u_unit, hu_unit⟩ := hM_unit
              have h_prod' : M * L'.prod = 0 := hprod
              rw [← hu_unit] at h_prod'
              calc L'.prod = 1 * L'.prod := by rw [one_mul]
              _ = (↑u_unit⁻¹ * ↑u_unit) * L'.prod := by rw [Units.inv_mul]
              _ = ↑u_unit⁻¹ * (↑u_unit * L'.prod) := by rw [mul_assoc]
              _ = ↑u_unit⁻¹ * 0 := by rw [h_prod']
              _ = 0 := mul_zero _
            by_cases hL'_nil : L' = []
            · subst hL'_nil
              simp only [List.prod_nil] at hL'_prod
              exact (not_isUnit_zero (hL'_prod ▸ isUnit_one)).elim
            · have hlen' : L'.length < (M :: L').length := by simp
              exact ih L'.length hlen' L' rfl hL'_nil (fun X hX => hmem X (List.mem_cons_of_mem M hX)) hL'_prod
          · have hM_R : M = R_Q := by
              have := hmem M (List.mem_cons.mpr (Or.inl rfl))
              cases this with
              | inl h => exact (hM h).elim
              | inr h => exact Set.mem_singleton_iff.mp h
            subst hM_R
            by_cases hR_in : R_Q ∈ L'
            · obtain ⟨as, bs, hL'_eq, has_not_R⟩ := rank_one_conversion_list_split_first R_Q L' hR_in
              have has_in_G : ∀ X ∈ as, X ∈ 𝒢 := by
                intro X hX
                have hX_mem : X ∈ (R_Q :: L') := by
                  rw [hL'_eq]
                  simp only [List.mem_cons, List.mem_append]
                  right; left; exact hX
                have := hmem X hX_mem
                cases this with
                | inl h => exact h
                | inr h =>
                  have : X = R_Q := Set.mem_singleton_iff.mp h
                  subst this; exact (has_not_R hX).elim
              have h_prod : (R_Q :: L').prod = (lam_Q ⬝ᵥ (as.prod *ᵥ u_Q)) • (R_Q :: bs).prod := by
                have : R_Q :: L' = R_Q :: as ++ R_Q :: bs := by rw [hL'_eq]; rfl
                rw [this]
                calc (R_Q :: as ++ R_Q :: bs).prod
                  _ = (R_Q * as.prod * R_Q) * bs.prod := by simp [mul_assoc]
                  _ = ((lam_Q ⬝ᵥ (as.prod *ᵥ u_Q)) • R_Q) * bs.prod := by rw [hR_Q, matrix_rank_one_sandwich_identity]
                  _ = (lam_Q ⬝ᵥ (as.prod *ᵥ u_Q)) • (R_Q * bs.prod) := by simp
                  _ = (lam_Q ⬝ᵥ (as.prod *ᵥ u_Q)) • (R_Q :: bs).prod := by simp
              have h_prod_zero := h_prod
              rw [hprod] at h_prod_zero
              cases smul_eq_zero.mp h_prod_zero.symm with
              | inl hc =>
                refine ⟨as, has_in_G, (hmap_eq as has_in_G).mpr hc⟩
              | inr hbs_prod =>
                have hbs_len : (R_Q :: bs).length < (R_Q :: L').length := by
                  rw [hL'_eq]
                  simp
                have hbs_mem : ∀ X ∈ R_Q :: bs, X ∈ 𝒢 ∪ {R_Q} := by
                  intro X hX
                  apply hmem
                  rw [hL'_eq]
                  simp only [List.mem_cons, List.mem_append]
                  rcases List.mem_cons.mp hX with rfl | hX
                  · left; rfl
                  · right; right; right; exact hX
                exact ih (R_Q :: bs).length hbs_len (R_Q :: bs) rfl (by simp) hbs_mem hbs_prod
            · -- R_Q ∉ L'
              have hL'_in_G : ∀ X ∈ L', X ∈ 𝒢 := by
                intro X hX
                have := hmem X (List.mem_cons_of_mem R_Q hX)
                cases this with
                | inl h => exact h
                | inr h =>
                  have : X = R_Q := Set.mem_singleton_iff.mp h
                  subst this; exact (hR_in hX).elim
              have hL'_unit : IsUnit L'.prod := List.prod_isUnit (fun X hX => h𝒢_inv X (hL'_in_G X hX))
              have hR_zero : R_Q = 0 := by
                obtain ⟨u_unit, hu_unit⟩ := hL'_unit
                simp only [List.prod_cons] at hprod
                rw [← hu_unit] at hprod
                calc R_Q = R_Q * 1 := by rw [mul_one]
                _ = R_Q * (↑u_unit * ↑u_unit⁻¹) := by rw [Units.mul_inv]
                _ = (R_Q * ↑u_unit) * ↑u_unit⁻¹ := by rw [mul_assoc]
                _ = 0 * ↑u_unit⁻¹ := by rw [hprod]
                _ = 0 := zero_mul _
              exact (hR_ne hR_zero).elim
    exact h_ind L hL_ne hL_mem hL_prod
  · rintro ⟨W, hW_mem, hW_map⟩
    rw [hmap_eq W hW_mem] at hW_map
    refine ⟨[R_Q] ++ W ++ [R_Q], by simp, ?_, ?_⟩
    · intro M hM
      simp only [List.mem_append, List.mem_singleton, Set.mem_union, Set.mem_singleton_iff] at hM ⊢
      rcases hM with (rfl | hM) | rfl
      · right; rfl
      · left; exact hW_mem M hM
      · right; rfl
    · calc ([R_Q] ++ W ++ [R_Q]).prod
        _ = R_Q * W.prod * R_Q := by simp [mul_assoc]
        _ = (lam_Q ⬝ᵥ (W.prod *ᵥ u_Q)) • R_Q := by rw [hR_Q, matrix_rank_one_sandwich_identity]
        _ = (0 : ℚ) • R_Q := by rw [hW_map]
        _ = 0 := zero_smul ℚ R_Q
