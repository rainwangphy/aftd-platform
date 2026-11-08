import AFTD.Prelude
import AFTD.Kb.NumberTheory.IsPrimitiveIntVec

/-!
# is_primitive_int_vec_abs

Topic: elementary_number_theory   Node: 9dfad0c704c1

Provenance: helper lemma. arXiv:2610.37711 Proposition 4.4 proof

For an integer vector z in ℤ^n, if z is primitive (every common natural divisor of all coordinates divides 1), then its coordinatewise absolute value |z| is also primitive.
-/

/-- The coordinatewise absolute value of a primitive integer vector is primitive. -/
theorem is_primitive_int_vec_abs (n : ℕ) (z : Fin n → ℤ) (hz : is_primitive_int_vec n z) :
    is_primitive_int_vec n (fun i => |z i|) := fun d hd => hz d fun i => (dvd_abs (d : ℤ) (z i)).mp (hd i)
