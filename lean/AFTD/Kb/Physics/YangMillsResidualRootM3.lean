import AFTD.Prelude
import AFTD.Kb.Physics.YangMillsResidualPolynomial

/-!
# yang_mills_residual_root_m3

Topic: classical_fields   Node: ad9e0cb3ae25

Provenance: formalization of a published result. Source: arXiv:2610.36784, Section 3

The rational residual polynomial yang_mills_residual_polynomial 3 evaluated at the rational number 1/21 equals 0.
-/

/-- The rational number 1/21 is a root of the residual polynomial S_3. -/
theorem yang_mills_residual_root_m3 :
    (yang_mills_residual_polynomial 3).eval (1 / 21 : ℚ) = 0 := by
  have hS : yang_mills_residual_polynomial 3
      = Polynomial.C (42525/32) * Polynomial.X - Polynomial.C (2025/32) := by
    have hbl : yang_mills_residual_polynomial.b_list 3 3 =
        ([1,
          Polynomial.C (3/2) - Polynomial.C (3/2) * Polynomial.X,
          Polynomial.C (81/16) * Polynomial.X^2 - Polynomial.C (45/8) * Polynomial.X + Polynomial.C (9/16),
          -Polynomial.C (1053/32) * Polynomial.X^3 + Polynomial.C (1431/32) * Polynomial.X^2
            - Polynomial.C (375/32) * Polynomial.X - Polynomial.C (3/32)] : List (Polynomial ℚ)) := by
      simp only [yang_mills_residual_polynomial.b_list.eq_def,
        yang_mills_residual_polynomial.cube_sum.eq_def]
      norm_num [Finset.sum_range_succ]
      refine ⟨?_, ?_, ?_⟩ <;> polynomial
    have hcs : yang_mills_residual_polynomial.cube_sum
        ([1,
          Polynomial.C (3/2) - Polynomial.C (3/2) * Polynomial.X,
          Polynomial.C (81/16) * Polynomial.X^2 - Polynomial.C (45/8) * Polynomial.X + Polynomial.C (9/16),
          -Polynomial.C (1053/32) * Polynomial.X^3 + Polynomial.C (1431/32) * Polynomial.X^2
            - Polynomial.C (375/32) * Polynomial.X - Polynomial.C (3/32)] : List (Polynomial ℚ)) 3 =
        -Polynomial.C (4725/32) * Polynomial.X^3 + Polynomial.C (7695/32) * Polynomial.X^2
          - Polynomial.C (3231/32) * Polynomial.X + Polynomial.C (261/32) := by
      simp only [yang_mills_residual_polynomial.cube_sum.eq_def]
      norm_num [Finset.sum_range_succ]
      polynomial
    unfold yang_mills_residual_polynomial
    simp only [hbl, hcs]
    norm_num
    have hnum :
        (-((3 : ℚ) • (-(Polynomial.C (1053 / 32) * Polynomial.X ^ 3)
              + Polynomial.C (1431 / 32) * Polynomial.X ^ 2
              - Polynomial.C (375 / 32) * Polynomial.X - Polynomial.C (3 / 32))) -
              (9 : ℚ) • (Polynomial.X * (-(Polynomial.C (4725 / 32) * Polynomial.X ^ 3)
              + Polynomial.C (7695 / 32) * Polynomial.X ^ 2
              - Polynomial.C (3231 / 32) * Polynomial.X + Polynomial.C (261 / 32))) : Polynomial ℚ)
          = (Polynomial.X - 1) * (Polynomial.C (42525/32) * Polynomial.X^3
              - Polynomial.C (23571/32) * Polynomial.X^2
              + Polynomial.C (1215/32) * Polynomial.X - Polynomial.C (9/32)) := by
      polynomial
    rw [hnum]
    rw [Polynomial.mul_divByMonic_cancel_left (q := Polynomial.X - 1) _
      (Polynomial.monic_X_sub_C (1:ℚ))]
    have hQS : (Polynomial.C (42525/32) * Polynomial.X^3 - Polynomial.C (23571/32) * Polynomial.X^2
        + Polynomial.C (1215/32) * Polynomial.X - Polynomial.C (9/32) : Polynomial ℚ)
        = (Polynomial.X ^ 2 + -(Polynomial.C (38 / 75) * Polynomial.X) + Polynomial.C (1 / 225))
          * (Polynomial.C (42525/32) * Polynomial.X - Polynomial.C (2025/32)) := by
      polynomial
    rw [hQS]
    rw [Polynomial.mul_divByMonic_cancel_left
      (q := Polynomial.X ^ 2 + -(Polynomial.C (38 / 75) * Polynomial.X) + Polynomial.C (1 / 225))
      _ (by monicity <;> norm_num)]
  rw [hS]
  simp
  norm_num
