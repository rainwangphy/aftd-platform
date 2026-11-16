import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixQPermanent
import AFTD.Kb.Tcs.MatrixQPermanentDiagonalConj
import AFTD.Kb.Tcs.MatrixQPermanentTwoOfIsSymm
import AFTD.Kb.Tcs.MatrixQPermanentThreeOfDiagOne
import AFTD.Kb.Tcs.CubicPolyStrictMonoOfMinorsLtOne

/-!
# matrix_q_permanent_strict_mono_of_order_le_three

Topic: combinatorics   Node: ac62dd43c0f3

Provenance: formalization of a published result. Source: arXiv:2611.14694 Proposition 5.1 -- Real positive definite counterexamples to a monotonicity conjecture for the q-permanent

If A is a non-diagonal real positive definite matrix of order n ≤ 3, then the function mapping q to the q-permanent of A is strictly increasing on all of ℝ.
-/

lemma matrix_q_permanent_strict_mono_of_order_le_three_case_two
    (A : Matrix (Fin 2) (Fin 2) ℝ) (hpos : A.PosDef) (hnondiag : ¬ A.IsDiag) :
    StrictMono (fun q : ℝ => matrix_q_permanent q A) := by
  have hsymm : A.IsSymm := by
    rw [← Matrix.isHermitian_iff_isSymm]
    exact hpos.isHermitian
  have hperm : ∀ q, matrix_q_permanent q A = A 0 0 * A 1 1 + q * (A 0 1) ^ 2 :=
    fun q => matrix_q_permanent_two_of_is_symm q A hsymm
  have hne : A 0 1 ≠ 0 := by
    intro hzero
    apply hnondiag
    intro i j hij
    fin_cases i <;> fin_cases j
    · contradiction
    · exact hzero
    · rw [← hsymm.apply]; exact hzero
    · contradiction
  have hsq_pos : 0 < (A 0 1) ^ 2 := sq_pos_of_ne_zero hne
  intro x y hxy
  dsimp only
  rw [hperm x, hperm y]
  nlinarith

lemma matrix_q_permanent_strict_mono_of_order_le_three_case_three
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hpos : A.PosDef) (hnondiag : ¬ A.IsDiag) :
    StrictMono (fun q : ℝ => matrix_q_permanent q A) := by
  have hsymm : A.IsSymm := by
    rw [← Matrix.isHermitian_iff_isSymm]
    exact hpos.isHermitian
  let d : Fin 3 → ℝ := fun k => (Real.sqrt (A k k))⁻¹
  have hd_pos : ∀ i, 0 < d i := fun i => inv_pos.mpr (Real.sqrt_pos.mpr hpos.diag_pos)
  have hd_ne : ∀ i, d i ≠ 0 := fun i => ne_of_gt (hd_pos i)
  let B := Matrix.diagonal d * A * Matrix.diagonal d
  have hBsymm : B.IsSymm := by
    ext i j
    dsimp [B]
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
    rw [hsymm.apply i j]
    ring
  have hBdiag : ∀ i, B i i = 1 := by
    intro i
    dsimp [B]
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
    have hposi : 0 < A i i := hpos.diag_pos
    have hsq : (Real.sqrt (A i i)) ^ 2 = A i i := Real.sq_sqrt (le_of_lt hposi)
    have : (Real.sqrt (A i i))⁻¹ * A i i * (Real.sqrt (A i i))⁻¹ =
      A i i * ((Real.sqrt (A i i))⁻¹ * (Real.sqrt (A i i))⁻¹) := by ring
    rw [this, ← mul_inv, ← sq, hsq, mul_inv_cancel₀ (ne_of_gt hposi)]
  let x := B 0 1
  let y := B 1 2
  let z := B 0 2
  have hminor : ∀ i j : Fin 3, i ≠ j → (B i j) ^ 2 < 1 := by
    intro i j hij
    have hposi : 0 < A i i := hpos.diag_pos
    have hposj : 0 < A j j := hpos.diag_pos
    have hij_sq : A i j ^ 2 < A i i * A j j := by
      let e : Fin 2 → Fin 3 := ![i, j]
      have he : Function.Injective e := by
        intro a b hab
        fin_cases a <;> fin_cases b
        · rfl
        · exfalso; apply hij; exact hab
        · exfalso; apply hij; exact hab.symm
        · rfl
      have hsub := hpos.submatrix he
      have hdet := Matrix.PosDef.det_pos hsub
      rw [Matrix.det_fin_two] at hdet
      have h10 : A j i = A i j := hsymm.apply i j
      change (A i i) * (A j j) - (A i j) * (A j i) > 0 at hdet
      rw [h10] at hdet
      linarith
    dsimp [B]
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
    have hsqi : (Real.sqrt (A i i)) ^ 2 = A i i := Real.sq_sqrt (le_of_lt hposi)
    have hsqj : (Real.sqrt (A j j)) ^ 2 = A j j := Real.sq_sqrt (le_of_lt hposj)
    have : ((Real.sqrt (A i i))⁻¹ * A i j * (Real.sqrt (A j j))⁻¹) ^ 2 =
        A i j ^ 2 / (A i i * A j j) := by
      rw [mul_pow, mul_pow, inv_pow, inv_pow, hsqi, hsqj]
      ring
    rw [this]
    have hprod_pos : 0 < A i i * A j j := mul_pos hposi hposj
    exact (div_lt_one hprod_pos).mpr hij_sq
  have hx : x ^ 2 < 1 := hminor 0 1 (by decide)
  have hy : y ^ 2 < 1 := hminor 1 2 (by decide)
  have hne : (x, y, z) ≠ (0, 0, 0) := by
    intro hzero
    obtain ⟨hx0, hyz⟩ := Prod.mk.inj hzero
    obtain ⟨hy0, hz0⟩ := Prod.mk.inj hyz
    dsimp only [x, y, z, B] at hx0 hy0 hz0
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at hx0 hy0 hz0
    have mul_cancel_both {u v : ℝ} (hu : u ≠ 0) (hv : v ≠ 0) {w : ℝ} (h : u * w * v = 0) : w = 0 := by
      have : u * (w * v) = 0 := by linarith
      cases mul_eq_zero.mp this with
      | inl h1 => exact False.elim (hu h1)
      | inr h1 =>
        cases mul_eq_zero.mp h1 with
        | inl h2 => exact h2
        | inr h2 => exact False.elim (hv h2)
    have ha01 : A 0 1 = 0 := mul_cancel_both (hd_ne 0) (hd_ne 1) hx0
    have ha12 : A 1 2 = 0 := mul_cancel_both (hd_ne 1) (hd_ne 2) hy0
    have ha02 : A 0 2 = 0 := mul_cancel_both (hd_ne 0) (hd_ne 2) hz0
    apply hnondiag
    intro i j hij
    fin_cases i <;> fin_cases j
    · contradiction
    · exact ha01
    · exact ha02
    · rw [← hsymm.apply]; exact ha01
    · contradiction
    · exact ha12
    · rw [← hsymm.apply]; exact ha02
    · rw [← hsymm.apply]; exact ha12
    · contradiction
  have hmonoB := cubic_poly_strict_mono_of_minors_lt_one x y z hx hy hne
  have hBpoly : ∀ q, matrix_q_permanent q B = 1 + (x ^ 2 + y ^ 2) * q + 2 * x * y * z * q ^ 2 + z ^ 2 * q ^ 3 :=
    fun q => matrix_q_permanent_three_of_diag_one B hBsymm hBdiag q
  have hB_strict : StrictMono (fun q => matrix_q_permanent q B) := by
    intro u v huv
    have := hmonoB huv
    dsimp only at this
    rw [← hBpoly u, ← hBpoly v] at this
    exact this
  have hconj : ∀ q, matrix_q_permanent q B = (Matrix.diagonal d).det ^ 2 * matrix_q_permanent q A :=
    fun q => matrix_q_permanent_diagonal_conj q A d
  have hdet_pos : 0 < (Matrix.diagonal d).det := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_pos fun i _ => hd_pos i
  have hc_pos : 0 < (Matrix.diagonal d).det ^ 2 := sq_pos_of_pos hdet_pos
  intro u v huv
  have hlt := hB_strict huv
  dsimp only at hlt
  rw [hconj u, hconj v] at hlt
  exact (mul_lt_mul_iff_of_pos_left hc_pos).mp hlt

/-- The q-permanent of a non-diagonal real positive definite matrix of order at most 3 is strictly increasing on ℝ. -/
theorem matrix_q_permanent_strict_mono_of_order_le_three
    (n : ℕ) (hn : n ≤ 3) (A : Matrix (Fin n) (Fin n) ℝ)
    (hpos : A.PosDef) (hnondiag : ¬ A.IsDiag) :
    StrictMono (fun q : ℝ => matrix_q_permanent q A) := by
  interval_cases n
  · exfalso
    apply hnondiag
    intro i
    exact i.elim0
  · exfalso
    apply hnondiag
    intro i j hij
    exfalso
    apply hij
    ext
    omega
  · exact matrix_q_permanent_strict_mono_of_order_le_three_case_two A hpos hnondiag
  · exact matrix_q_permanent_strict_mono_of_order_le_three_case_three A hpos hnondiag
