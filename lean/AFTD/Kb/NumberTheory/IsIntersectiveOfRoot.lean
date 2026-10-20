import AFTD.Prelude
import AFTD.Kb.NumberTheory.IsIntersective

/-!
# is_intersective_of_root

Topic: elementary_number_theory   Node: 1a41d2f0727b

Provenance: helper lemma. step towards op_153_subexp_bound_intersective_quadratic

Every integer polynomial with an integer root has a root modulo every positive integer m.
-/

/-- An integer polynomial with an integer root is intersective. -/
theorem is_intersective_of_root (h : Polynomial ℤ) (r : ℤ) (hr : h.eval r = 0) :
    is_intersective h := by
  intro m _
  use r
  rw [hr]
