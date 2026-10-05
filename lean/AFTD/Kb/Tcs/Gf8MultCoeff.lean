import AFTD.Prelude

/-!
# gf8_mult_coeff

Topic: quantum   Node: 592dc819e975

The structure constants for multiplication in GF(8) with respect to the basis {1, alpha, alpha^2} with irreducible polynomial alpha^3 + alpha + 1.
-/

/-- Multiplication structure constants of GF(8) in the polynomial basis with alpha^3 = alpha + 1. -/
def gf8_mult_coeff (q r l : Fin 3) : ZMod 2 := match q.val + r.val, l.val with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 0 => 1 | 3, 1 => 1 | 4, 1 => 1 | 4, 2 => 1 | _, _ => 0
