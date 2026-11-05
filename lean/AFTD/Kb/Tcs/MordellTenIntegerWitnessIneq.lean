import AFTD.Prelude
import AFTD.Kb.Tcs.MordellTenIntegerNormSum

/-!
# mordell_ten_integer_witness_ineq

Topic: combinatorics   Node: 2fa8856df9a6

Provenance: formalization of a published result. Source: arXiv:2611.03088 eq. (8)

For the ten integer points W = ![(11183, 0), (-11183, 0), (32765, 14669), (32765, -14669), (-32765, 14669), (-32765, -14669), (12323, 31572), (12323, -31572), (-12323, 31572), (-12323, -31572)] in Fin 10 → ℤ × ℤ and q = 9999608174, 9^36 times the product over all i < j in Fin 10 of the squared Euclidean distances ((W i).1 - (W j).1)^2 + ((W i).2 - (W j).2)^2 is strictly greater than q^45.
-/

/-- Exact integer certificate that 9^36 times the pairwise squared distance product exceeds q^45 for q = 9999608174. -/
lemma mordell_ten_integer_witness_ineq :
    let W : Fin 10 → ℤ × ℤ := ![(11183, 0), (-11183, 0),
      (32765, 14669), (32765, -14669), (-32765, 14669), (-32765, -14669),
      (12323, 31572), (12323, -31572), (-12323, 31572), (-12323, -31572)]
    let q : ℤ := 9999608174
    (9 : ℤ) ^ 36 * ∏ i : Fin 10, ∏ j : Fin 10 with i < j,
      (((W i).1 - (W j).1) ^ 2 + ((W i).2 - (W j).2) ^ 2) > q ^ 45 := by first | (simp_all; done) | omega | decide | linarith | positivity | (aesop; done)
