import AFTD.Prelude
import AFTD.Kb.Tcs.Op1370AdjugateTopZero

/-!
# op1370_adjugate_leading

Topic: combinatorics   Node: 361076b0d11b

Provenance: helper lemma.

The next coefficient of the adjugate of XI plus a constant matrix is the identity matrix.
-/

open Matrix Polynomial
open scoped BigOperators

theorem op1370_adjugate_leading
    {ι : Type*} [Fintype ι] [DecidableEq ι] (J : Matrix ι ι ℚ) (i j : ι) :
    (((Polynomial.X : ℚ[X]) • (1 : Matrix ι ι ℚ[X]) + J.map Polynomial.C).adjugate i j).coeff
      (Fintype.card ι - 1) = (1 : Matrix ι ι ℚ) i j := by
  classical
  let A : Matrix ι ι ℚ[X] := (Polynomial.X : ℚ[X]) • 1 + J.map Polynomial.C
  have hpos : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
  obtain ⟨k, hk⟩ : ∃ k, Fintype.card ι = k + 1 := ⟨Fintype.card ι - 1, by omega⟩
  have hz (a b : ι) : (A.adjugate a b).coeff (Fintype.card ι) = 0 := by
    exact op1370_adjugate_top_zero J a b
  have hdet : A.det.coeff (Fintype.card ι) = 1 := by
    simpa [A] using (Polynomial.coeff_det_X_add_C_card (1 : Matrix ι ι ℚ) J)
  have hmul : A.adjugate * A =
      (Polynomial.X : ℚ[X]) • A.adjugate + A.adjugate * J.map Polynomial.C := by
    dsimp [A]
    rw [mul_add, mul_smul_comm, mul_one]
  have heq := congrArg (fun M : Matrix ι ι ℚ[X] => (M i j).coeff (Fintype.card ι))
    (Matrix.adjugate_mul A)
  rw [hmul] at heq
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Polynomial.coeff_add,
    Matrix.mul_apply, Polynomial.finsetSum_coeff, Matrix.map_apply, Polynomial.coeff_mul_C,
    hz, zero_mul, Finset.sum_const_zero, add_zero] at heq
  rw [hk, Polynomial.coeff_X_mul] at heq
  have : Fintype.card ι - 1 = k := by omega
  rw [this]
  by_cases hij : i = j
  · subst j
    simpa [Matrix.one_apply, ← hk, hdet] using heq
  · simpa [Matrix.one_apply, hij] using heq
