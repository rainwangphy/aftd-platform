import AFTD.Prelude

/-!
# matrix_det_eq_permanent_of_char_two

Topic: algebraic_complexity   Node: eeb362633814

Provenance: formalization of a published result. Source: Valiant 1979, 'Completeness classes in algebra', STOC 1979, Sec. 3

For every commutative ring R of characteristic 2 and any square matrix M over R indexed by a finite type n with decidable equality, the determinant of M equals the permanent of M.
-/

/-- Over any commutative ring of characteristic 2, the determinant of any square matrix equals its permanent. -/
theorem matrix_det_eq_permanent_of_char_two {n R : Type*} [DecidableEq n] [Fintype n] [CommRing R] [CharP R 2] (M : Matrix n n R) : M.det = M.permanent := by
  rw [Matrix.det_apply', Matrix.permanent]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  have hsign : (↑↑(Equiv.Perm.sign σ) : R) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h]
    · simp
    · simp [CharTwo.neg_eq]
  rw [hsign, one_mul]
