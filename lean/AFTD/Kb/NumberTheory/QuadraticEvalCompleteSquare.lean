import AFTD.Prelude

/-!
# quadratic_eval_complete_square

Topic: elementary_number_theory   Node: 9673f16b47a7

Provenance: helper lemma. step towards op_153_subexp_bound_intersective_quadratic

For any degree-2 integer polynomial $h$, $4 a h(x) = (2ax + b)^2 - \Delta$, where $a = h_2, b = h_1, c = h_0$ and $\Delta = b^2 - 4ac$ is the discriminant.
-/

/-- For any degree-2 integer polynomial h, 4 * a * h(x) = (2 * a * x + b)^2 - discr(a, b, c), where a = h.coeff 2, b = h.coeff 1, c = h.coeff 0. -/
theorem quadratic_eval_complete_square (h : Polynomial ℤ) (hdeg : h.degree = 2) (x : ℤ) :
    4 * h.coeff 2 * h.eval x = (2 * h.coeff 2 * x + h.coeff 1) ^ 2 - discrim (h.coeff 2) (h.coeff 1) (h.coeff 0) := by
  have h2 : h.eval x = h.coeff 2 * x ^ 2 + h.coeff 1 * x + h.coeff 0 := by
    have := congr_arg (Polynomial.eval x) (Polynomial.eq_quadratic_of_degree_le_two hdeg.le)
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X] at this
    exact this
  rw [h2]
  unfold discrim
  ring
