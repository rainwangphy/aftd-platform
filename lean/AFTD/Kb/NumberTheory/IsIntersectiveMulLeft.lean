import AFTD.Prelude
import AFTD.Kb.NumberTheory.IsIntersective

/-!
# is_intersective_mul_left

Topic: elementary_number_theory   Node: 6eca4ce40cfe

Provenance: helper lemma. step towards op_153_subexp_bound_intersective_quadratic

For any polynomials g, h ∈ ℤ[X], if h is intersective then g * h is intersective.
-/

/-- A multiple of an intersective polynomial is intersective. -/
theorem is_intersective_mul_left (g h : Polynomial ℤ) (hh : is_intersective h) :
    is_intersective (g * h) := by
  intro m hm
  obtain ⟨n, hn⟩ := hh m hm
  use n
  rw [Polynomial.eval_mul]
  rw [Int.modEq_zero_iff_dvd] at hn ⊢
  exact dvd_mul_of_dvd_right hn _
