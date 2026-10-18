import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.MatrixUnitDifferenceRowsIsTotallyUnimodular
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# midpoint_certificate_matrix_minor_abs_le

Topic: combinatorics   Node: d84fafba8afd

Provenance: helper lemma. step towards finset_card_ge_one_add_clog_of_midpoint_balanced

The absolute value of every k x k minor of a (k+1) x (k+1) midpoint-certificate matrix is bounded by 2^k, proved by multilinear expansion into 2^k unit-difference determinants and applying total unimodularity.
-/

/-- The absolute value of every k x k minor of a (k+1) x (k+1) midpoint-certificate matrix is bounded by 2^k. -/
theorem midpoint_certificate_matrix_minor_abs_le {k : ℕ} (u v : Fin (k + 1) → Fin (k + 1))
    (i₀ j₀ : Fin (k + 1)) :
    |((Matrix.of fun (i j : Fin (k + 1)) =>
        (if j = i then (2 : ℤ) else 0) - (if j = u i then 1 else 0) - (if j = v i then 1 else 0)).submatrix
        i₀.succAbove j₀.succAbove).det| ≤ (2 ^ k : ℤ) := by
  set m : Matrix (Fin k) (Fin k) ℤ := Matrix.of fun (r c : Fin k) =>
      (if j₀.succAbove c = i₀.succAbove r then (1 : ℤ) else 0) -
      (if j₀.succAbove c = u (i₀.succAbove r) then 1 else 0)
  set m' : Matrix (Fin k) (Fin k) ℤ := Matrix.of fun (r c : Fin k) =>
      (if j₀.succAbove c = i₀.succAbove r then (1 : ℤ) else 0) -
      (if j₀.succAbove c = v (i₀.succAbove r) then 1 else 0)
  have hsplit : ((Matrix.of fun (i j : Fin (k + 1)) =>
        (if j = i then (2 : ℤ) else 0) - (if j = u i then 1 else 0) - (if j = v i then 1 else 0)).submatrix
        i₀.succAbove j₀.succAbove) = m + m' := by
    ext r c
    simp only [m, m', Matrix.submatrix_apply, Matrix.of_apply, Matrix.add_apply]
    split_ifs <;> ring
  rw [hsplit]
  have hexp : (m + m').det = ∑ s : Finset (Fin k), Matrix.det (s.piecewise m m') := by
    have := MultilinearMap.map_add_univ Matrix.detRowAlternating.toMultilinearMap m m'
    exact this
  rw [hexp]
  have hbound : ∀ s : Finset (Fin k), |Matrix.det (s.piecewise m m')| ≤ 1 := by
    intro s
    set w : Fin k → Fin (k + 1) := fun r => if r ∈ s then u (i₀.succAbove r) else v (i₀.succAbove r)
    set B : Matrix (Fin k) (Fin (k + 1)) ℤ := Matrix.of fun (r : Fin k) (j : Fin (k + 1)) =>
      (Pi.single (i₀.succAbove r) (1 : ℤ) : Fin (k + 1) → ℤ) j - (Pi.single (w r) (1 : ℤ) : Fin (k + 1) → ℤ) j
    have heq : (s.piecewise m m' : Matrix (Fin k) (Fin k) ℤ) = B.submatrix id j₀.succAbove := by
      ext r c
      have hrow : (Finset.piecewise s m m' : Matrix (Fin k) (Fin k) ℤ) r = if r ∈ s then m r else m' r := by
        split_ifs with hr
        · exact Finset.piecewise_eq_of_mem s m m' hr
        · exact Finset.piecewise_eq_of_notMem s m m' hr
      rw [congrFun hrow c]
      rcases em (r ∈ s) with hr | hr
      · rw [if_pos hr]
        simp only [B, w, m, Matrix.submatrix_apply, Matrix.of_apply, id_eq, Pi.single_apply, if_pos hr]
      · rw [if_neg hr]
        simp only [B, w, m', Matrix.submatrix_apply, Matrix.of_apply, id_eq, Pi.single_apply, if_neg hr]
    rw [heq]
    have htu := matrix_unit_difference_rows_isTotallyUnimodular (fun r => i₀.succAbove r) w
    have hdet := htu k id j₀.succAbove Function.injective_id Fin.succAbove_right_injective
    rcases hdet with ⟨sgn, hsgn⟩
    rw [← hsgn]
    cases sgn <;> simp
  calc
    |∑ s : Finset (Fin k), Matrix.det (s.piecewise m m')| ≤
        ∑ s : Finset (Fin k), |Matrix.det (s.piecewise m m')| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s : Finset (Fin k), (1 : ℤ) := Finset.sum_le_sum (fun s _ => hbound s)
    _ = 2 ^ k := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
      push_cast
      rfl
