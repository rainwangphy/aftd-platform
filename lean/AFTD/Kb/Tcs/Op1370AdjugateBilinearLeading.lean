import AFTD.Prelude
import AFTD.Kb.Tcs.Op1370AdjugateLeading

/-!
# op1370_adjugate_bilinear_leading

Topic: combinatorics   Node: 723b017140d8

Provenance: helper lemma.

The top adjugate coefficient of a matrix bilinear form is the corresponding dot product.
-/

open Matrix Polynomial
open scoped BigOperators

theorem op1370_adjugate_bilinear_leading
    {ι : Type*} [Fintype ι] [DecidableEq ι] (J : Matrix ι ι ℚ)
    (u v : ι → ℚ) :
    (∑ a, ∑ b, Polynomial.C (u a) *
      ((Polynomial.X : ℚ[X]) • (1 : Matrix ι ι ℚ[X]) + J.map Polynomial.C).adjugate a b *
      Polynomial.C (v b)).coeff (Fintype.card ι - 1) = ∑ a, u a * v a := by
  classical
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_mul_C, Polynomial.coeff_C_mul,
    op1370_adjugate_leading, Matrix.one_apply]
  simp
