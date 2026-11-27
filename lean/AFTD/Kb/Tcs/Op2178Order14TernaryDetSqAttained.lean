import AFTD.Prelude

/-!
# op_2178_order_14_ternary_det_sq_attained

Topic: combinatorics   Node: b85ff1ba617f

Provenance: formalization of a published result. Source: arXiv:2611.27591: Determinantal upper bounds for ternary matrices, Section 4, lines 1269-1284

There exists a 14 by 14 matrix M with entries in the complex third roots of unity whose squared determinant Complex.normSq M.det equals 2^24 * 3^13 * 223, attained by the balanced normal matrix M_14.
-/

def op2178_m14_exp : Fin 14 → Fin 14 → Fin 3 :=
  ![![0,0,0,1,0,0, 2,2,0,1,1, 1,1,0],
    ![0,0,1,0,0,0, 2,1,1,0,2, 1,0,1],
    ![0,1,0,0,0,0, 1,2,1,2,0, 0,1,1],
    ![1,0,0,2,0,0, 1,1,2,2,2, 1,1,2],
    ![0,0,0,0,1,2, 1,2,2,1,2, 1,2,1],
    ![0,0,0,0,2,1, 2,1,2,2,1, 2,1,1],
    ![2,2,1,1,1,2, 0,1,0,2,0, 1,1,1],
    ![2,1,2,1,2,1, 1,0,0,0,2, 1,1,1],
    ![0,1,1,2,2,2, 0,0,2,0,0, 1,1,0],
    ![1,0,2,2,1,2, 2,0,0,0,0, 0,1,1],
    ![1,2,0,2,2,1, 0,2,0,0,0, 1,0,1],
    ![1,1,0,1,1,2, 1,1,1,0,1, 2,0,0],
    ![1,0,1,1,2,1, 1,1,1,1,0, 0,2,0],
    ![0,1,1,2,1,1, 1,1,0,1,1, 0,0,2]]

def op2178_blk (i : Fin 14) : Fin 3 := if i.val < 6 then 0 else if i.val < 11 then 1 else 2

def op2178_cnt (i j : Fin 14) (r : Fin 3) : ℕ :=
  (Finset.univ.filter fun k => op2178_m14_exp i k + 2 * op2178_m14_exp j k = r).card

theorem op2178_cnt_facts : ∀ i j : Fin 14,
    op2178_cnt i j 1 = op2178_cnt i j 2 ∧
    (op2178_cnt i j 0 : ℤ) - op2178_cnt i j 2 =
      (if i = j then 12 else 0) + (if op2178_blk i = op2178_blk j then 2 else -1) := by
  decide

theorem op2178_sum_fin3 {ι : Type*} [Fintype ι] (d : ι → Fin 3) (ζ : ℂ) :
    ∑ k, ζ ^ (d k).val =
      ((Finset.univ.filter fun k => d k = 0).card : ℂ) +
      ((Finset.univ.filter fun k => d k = 1).card : ℂ) * ζ +
      ((Finset.univ.filter fun k => d k = 2).card : ℂ) * ζ ^ 2 := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ d (fun k => ζ ^ (d k).val), Fin.sum_univ_three]
  have h : ∀ r : Fin 3, ∑ k ∈ Finset.univ.filter (fun k => d k = r), ζ ^ (d k).val =
      ((Finset.univ.filter fun k => d k = r).card : ℂ) * ζ ^ r.val := by
    intro r
    rw [Finset.sum_congr rfl (fun k hk => by rw [(Finset.mem_filter.1 hk).2]), Finset.sum_const,
      nsmul_eq_mul]
  rw [h 0, h 1, h 2]
  simp

/-- There exists an order-14 ternary matrix whose squared determinant equals 2^24 * 3^13 * 223. -/
theorem op_2178_order_14_ternary_det_sq_attained :
    ∃ (M : Matrix (Fin 14) (Fin 14) ℂ),
      (∀ i j, ∃ u : rootsOfUnity 3 ℂ, ((u : ℂˣ) : ℂ) = M i j) ∧
      Complex.normSq M.det = (2 : ℝ) ^ 24 * (3 : ℝ) ^ 13 * 223 := by
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (3 : ℕ)) with hζdef
  have hζ : IsPrimitiveRoot ζ 3 := Complex.isPrimitiveRoot_exp 3 (by norm_num)
  have h3 : ζ ^ 3 = 1 := hζ.pow_eq_one
  have hsum : 1 + ζ + ζ ^ 2 = 0 := by
    have := hζ.geom_sum_eq_zero (by norm_num)
    simpa [Finset.sum_range_succ] using this
  have hnorm : ‖ζ‖ = 1 := hζ.norm'_eq_one (by norm_num)
  have hstar : star ζ = ζ ^ 2 := by
    have hne : ζ ≠ 0 := hζ.ne_zero (by norm_num)
    have hmul : ζ * star ζ = 1 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]; simp
    have : ζ * ζ ^ 2 = 1 := by rw [← pow_succ']; exact h3
    exact mul_left_cancel₀ hne (hmul.trans this.symm)
  let M : Matrix (Fin 14) (Fin 14) ℂ := Matrix.of fun i j => ζ ^ (op2178_m14_exp i j).val
  refine ⟨M, ?_, ?_⟩
  · intro i j
    refine ⟨rootsOfUnity.mkOfPowEq (ζ ^ (op2178_m14_exp i j).val) ?_, ?_⟩
    · rw [← pow_mul, mul_comm, pow_mul, h3, one_pow]
    · rw [rootsOfUnity.coe_mkOfPowEq]; rfl
  · -- Gram matrix
    let P : Matrix (Fin 14) (Fin 3) ℂ := Matrix.of fun i b => if op2178_blk i = b then 1 else 0
    let C : Matrix (Fin 3) (Fin 3) ℂ := Matrix.of fun a b => if a = b then 2 else -1
    have hpow : ∀ x y : Fin 3, ζ ^ x.val * star (ζ ^ y.val) = ζ ^ (x + 2 * y).val := by
      intro x y
      rw [star_pow, hstar, ← pow_mul, ← pow_add]
      have : ∀ m : ℕ, ζ ^ m = ζ ^ (m % 3) := by
        intro m; conv_lhs => rw [← Nat.div_add_mod m 3, pow_add, pow_mul, h3, one_pow, one_mul]
      rw [this, this ((x + 2 * y).val)]
      congr 1
      fin_cases x <;> fin_cases y <;> rfl
    have hgram : M * M.conjTranspose = (12 : ℂ) • (1 : Matrix (Fin 14) (Fin 14) ℂ) + P * C * P.transpose := by
      ext i j
      have hl : (M * M.conjTranspose) i j =
          ∑ k, ζ ^ (op2178_m14_exp i k + 2 * op2178_m14_exp j k).val := by
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, M, Matrix.of_apply]
        exact Finset.sum_congr rfl (fun k _ => hpow _ _)
      have hr : ((12 : ℂ) • (1 : Matrix (Fin 14) (Fin 14) ℂ) + P * C * P.transpose : Matrix (Fin 14) (Fin 14) ℂ) i j =
          (if i = j then 12 else 0) + (if op2178_blk i = op2178_blk j then 2 else -1) := by
        simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.mul_apply,
          Matrix.transpose_apply, P, C, Matrix.of_apply, Fin.sum_univ_three]
        generalize op2178_blk i = bi
        generalize op2178_blk j = bj
        fin_cases bi <;> fin_cases bj <;> by_cases hij : i = j <;> simp [hij] <;> norm_num
      rw [hl, hr, op2178_sum_fin3]
      obtain ⟨h12, h02⟩ := op2178_cnt_facts i j
      simp only [op2178_cnt] at h12 h02
      rw [h12]
      have h02' : ((Finset.univ.filter fun k => op2178_m14_exp i k + 2 * op2178_m14_exp j k = 0).card : ℂ)
          = ((Finset.univ.filter fun k => op2178_m14_exp i k + 2 * op2178_m14_exp j k = 2).card : ℂ) +
            ((if i = j then 12 else 0) + (if op2178_blk i = op2178_blk j then 2 else -1) : ℤ) := by
        rw [← h02]; push_cast; ring
      rw [h02']
      have hz2 : ζ ^ 2 = -1 - ζ := by linear_combination hsum
      rw [hz2]
      push_cast
      split_ifs <;> ring
    have hdetG : (M * M.conjTranspose).det = (2 : ℂ) ^ 24 * 3 ^ 13 * 223 := by
      rw [hgram]
      have hfac : ((12 : ℂ) • (1 : Matrix (Fin 14) (Fin 14) ℂ) + P * C * P.transpose) =
          (12 : ℂ) • (1 + ((1 / 12 : ℂ) • (P * C)) * P.transpose) := by
        rw [smul_add, Matrix.smul_mul, smul_smul]
        norm_num
      rw [hfac, Matrix.det_smul, Matrix.det_one_add_mul_comm]
      have h3x3 : (1 : Matrix (Fin 3) (Fin 3) ℂ) + P.transpose * ((1 / 12 : ℂ) • (P * C)) =
          !![2, -1/2, -1/2; -5/12, 22/12, -5/12; -1/4, -1/4, 3/2] := by
        ext a b
        fin_cases a <;> fin_cases b <;>
          simp [Matrix.mul_apply, Fin.sum_univ_succ, P, C, op2178_blk, Matrix.one_apply] <;>
          norm_num
      rw [h3x3, Matrix.det_fin_three]
      simp
      norm_num
    have hdet : (Complex.normSq M.det : ℂ) = (M * M.conjTranspose).det := by
      rw [Matrix.det_mul, Matrix.det_conjTranspose, Complex.star_def, Complex.mul_conj]
    have := hdet.trans hdetG
    exact_mod_cast this
