import AFTD.Prelude
import AFTD.Kb.NumberTheory.NotIsIntersectiveSqAddOne

/-!
# digit_exchange_walsh_root_poly_eval

Topic: cryptography   Node: 411dc8c62033

Provenance: helper lemma. step towards op_1608_digit_exchange_walsh_le_six

Evaluating the root polynomial C(v^2) + (X^2+X+C c)^2 * (C(s^2) + C(t^2) X^2 + C t X) at a gives v^2 + (a^2+a+c)^2 (s^2 + t^2 a^2 + t a).
-/

theorem digit_exchange_walsh_root_poly_eval
    (m : ℕ) (c v s t a : GaloisField 2 m) :
    (Polynomial.C (v ^ 2) + (Polynomial.X ^ 2 + Polynomial.X + Polynomial.C c) ^ 2 *
      (Polynomial.C (s ^ 2) + Polynomial.C (t ^ 2) * Polynomial.X ^ 2 + Polynomial.C t * Polynomial.X)
      : Polynomial (GaloisField 2 m)).eval a
      = v ^ 2 + (a ^ 2 + a + c) ^ 2 * (s ^ 2 + t ^ 2 * a ^ 2 + t * a) := by first | exact not_is_intersective_sq_add_one | (apply not_is_intersective_sq_add_one <;> assumption) | (apply not_is_intersective_sq_add_one <;> simp_all) | simpa using not_is_intersective_sq_add_one
