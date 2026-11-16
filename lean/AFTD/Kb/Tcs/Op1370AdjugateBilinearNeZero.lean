import AFTD.Prelude
import AFTD.Kb.Tcs.Op1370AdjugateBilinearLeading

/-!
# op1370_adjugate_bilinear_ne_zero

Topic: combinatorics   Node: 536ad0da1b52

Provenance: helper lemma.

A nonzero dot product ensures that the corresponding adjugate bilinear form is a nonzero polynomial.
-/

open Matrix Polynomial
open scoped BigOperators

theorem op1370_adjugate_bilinear_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι] (J : Matrix ι ι ℚ)
    (u v : ι → ℚ) (h : (∑ a, u a * v a) ≠ 0) :
    (∑ a, ∑ b, Polynomial.C (u a) *
      ((Polynomial.X : ℚ[X]) • (1 : Matrix ι ι ℚ[X]) + J.map Polynomial.C).adjugate a b *
      Polynomial.C (v b)) ≠ 0 := by
  intro hzero
  have hc := op1370_adjugate_bilinear_leading J u v
  rw [hzero, Polynomial.coeff_zero] at hc
  exact h hc.symm
