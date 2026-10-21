import AFTD.Prelude

/-!
# root_lattice_form_pos_def

Topic: combinatorics   Node: 267e88b8fb67

Provenance: helper lemma. arXiv:2610.26970 (Gaussian Lower Bounds for Distinct Subset Sums in Higher Dimensions), Proposition 3.2: the positive-definiteness claim

The k×k matrix H = I_k − 11ᵀ/(k+1) is positive definite.
-/

theorem root_lattice_form_pos_def (k : ℕ) :
    (1 - (1 / ((k : ℝ) + 1)) • Matrix.of (fun _ _ : Fin k => (1 : ℝ))).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · apply Matrix.IsHermitian.ext
    intro i j
    simp [Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply, eq_comm]
  · intro x hx
    by_cases hk : k = 0
    · subst k
      exfalso
      apply hx
      funext i
      exact i.elim0
    · have hMx :
          Matrix.mulVec (1 - (1 / ((k : ℝ) + 1)) • Matrix.of (fun _ _ : Fin k => (1 : ℝ))) x
            = fun i => x i - (1 / ((k : ℝ) + 1)) * (∑ j, x j) := by
        funext i
        simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.one_apply,
          Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, sub_mul]
        rw [Finset.sum_sub_distrib]
        congr 1
        · simp
        · rw [← Finset.mul_sum]
          ring
      have hQ :
          dotProduct (star x) (fun i => x i - (1 / ((k : ℝ) + 1)) * (∑ j, x j))
            = (∑ i, x i ^ 2) - (1 / ((k : ℝ) + 1)) * (∑ i, x i)^2 := by
        simp only [dotProduct, star_trivial]
        simp only [mul_sub]
        rw [Finset.sum_sub_distrib]
        congr 1
        · simp [pow_two]
        · rw [← Finset.sum_mul]
          ring
      rw [hMx, hQ]
      have hcs : (∑ i, x i)^2 ≤ (k : ℝ) * ∑ i, x i^2 := by
        simpa using (sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin k))) (f := x))
      have hApos : 0 < ∑ i, x i ^ 2 := by
        have hne : ∃ i : Fin k, x i ≠ 0 := by
          by_contra h
          apply hx
          funext i
          by_contra hi
          exact h ⟨i, hi⟩
        obtain ⟨i, hi⟩ := hne
        exact Finset.sum_pos' (fun j _ => sq_nonneg (x j))
          ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩
      have hbound : (1 / ((k : ℝ) + 1)) * (∑ i, x i)^2 ≤
          ((k : ℝ) / ((k : ℝ) + 1)) * (∑ i, x i ^ 2) := by
        have hc : 0 ≤ 1 / ((k : ℝ) + 1) := by positivity
        calc
          (1 / ((k : ℝ) + 1)) * (∑ i, x i)^2 ≤
              (1 / ((k : ℝ) + 1)) * ((k : ℝ) * (∑ i, x i ^ 2)) :=
            mul_le_mul_of_nonneg_left hcs hc
          _ = ((k : ℝ) / ((k : ℝ) + 1)) * (∑ i, x i ^ 2) := by ring
      have hcoef : 0 < (1 : ℝ) - (k : ℝ) / ((k : ℝ) + 1) := by
        have h : (1 : ℝ) - (k : ℝ) / ((k : ℝ) + 1) = 1 / ((k : ℝ) + 1) := by
          field_simp
          ring
        rw [h]
        positivity
      nlinarith [mul_pos hcoef hApos]
