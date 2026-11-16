import AFTD.Prelude
import AFTD.Kb.Tcs.MonomialMul

/-!
# low_half_mul3_gate5_expansion

Topic: circuits   Node: def307619c6e

Provenance: helper lemma. arXiv:2611.15992 Section 3

Expansion of the sixth AND gate g_5 over GF(2): (g_1 + a_1)(g_2 + b_1) equals a_0 a_1 b_0 b_1 + g_1 + g_2 + a_1 b_1.
-/

/-- Algebraic expansion of gate g_5 over GF(2). -/
theorem low_half_mul3_gate5_expansion (v : Fin 6 → ZMod 2) :
    (v 0 * v 4 + v 1) * (v 1 * v 3 + v 4) =
      v 0 * v 1 * v 3 * v 4 + v 0 * v 4 + v 1 * v 3 + v 1 * v 4 := by
  have h4 : v 4 * v 4 = v 4 := monomial_mul_zmod2_mul_self (v 4)
  have h1 : v 1 * v 1 = v 1 := monomial_mul_zmod2_mul_self (v 1)
  linear_combination (v 0) * h4 + (v 3) * h1
