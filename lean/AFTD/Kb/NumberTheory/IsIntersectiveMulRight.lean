import AFTD.Prelude
import AFTD.Kb.NumberTheory.IsIntersective
import AFTD.Kb.NumberTheory.IsIntersectiveMulLeft

/-!
# is_intersective_mul_right

Topic: elementary_number_theory   Node: 630cd2ed98d2

Provenance: helper lemma. step towards op_153_subexp_bound_intersective_quadratic

If $g \in \mathbb{Z}[X]$ is intersective, then $g \cdot h$ is intersective for any $h \in \mathbb{Z}[X]$.
-/

/-- If g ∈ ℤ[X] is intersective, then g * h is intersective for any polynomial h. -/
theorem is_intersective_mul_right (g h : Polynomial ℤ) (hg : is_intersective g) :
    is_intersective (g * h) := by
  rw [mul_comm]
  exact is_intersective_mul_left h g hg
