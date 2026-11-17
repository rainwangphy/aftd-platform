import AFTD.Prelude

/-!
# real_pos_def_has_invertible_gram_factor

Topic: quantum   Node: 4f47c02d120c

Provenance: helper lemma. arXiv:2611.19367v1, Section III D–E, positive-definite factorization and singular-case extension.

Every finite real positive-definite matrix is the Gram matrix Fᵀ F of an invertible real square matrix F.
-/

theorem real_pos_def_has_invertible_gram_factor {n : Type*} [Fintype n] [DecidableEq n] (H : Matrix n n ℝ) (hH : H.PosDef) : ∃ F : Matrix n n ℝ, IsUnit F.det ∧ F.transpose * F = H := by
  classical
  letI : PartialOrder (Matrix n n ℝ) := Matrix.instPartialOrder
  letI : StarOrderedRing (Matrix n n ℝ) := Matrix.instStarOrderedRing
  letI : NonnegSpectrumClass ℝ (Matrix n n ℝ) := Matrix.instNonnegSpectrumClass
  refine ⟨CFC.sqrt H, ?_, ?_⟩
  · have hsq : (CFC.sqrt H) * (CFC.sqrt H) = H := by
      simpa [pow_two] using
        CFC.sq_sqrt H (IsStrictlyPositive.nonneg (Matrix.PosDef.isStrictlyPositive hH))
    have hprod : IsUnit ((CFC.sqrt H) * (CFC.sqrt H)) := by
      rw [hsq]
      exact Matrix.PosDef.isUnit hH
    have hFunit : IsUnit (CFC.sqrt H) := isUnit_of_mul_isUnit_left hprod
    rwa [← Matrix.isUnit_iff_isUnit_det]
  · have hsq : (CFC.sqrt H) * (CFC.sqrt H) = H := by
      simpa [pow_two] using
        CFC.sq_sqrt H (IsStrictlyPositive.nonneg (Matrix.PosDef.isStrictlyPositive hH))
    have hF : IsSelfAdjoint (CFC.sqrt H) := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg H)
    have hstar : star (CFC.sqrt H) = CFC.sqrt H := hF
    have htr : (CFC.sqrt H).transpose = CFC.sqrt H := by
      rw [Matrix.star_eq_conjTranspose] at hstar
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hstar
    rw [htr, hsq]
