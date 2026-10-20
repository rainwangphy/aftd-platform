import AFTD.Prelude
import AFTD.Kb.NumberTheory.IsIntersective

/-!
# is_intersective_comp_X_add_C

Topic: elementary_number_theory   Node: 9e06c188f54b

Provenance: helper lemma. step towards op_153_subexp_bound_intersective_quadratic

If $h \in \mathbb{Z}[X]$ is intersective, then the translated polynomial $h(X + c)$ is also intersective for any integer $c$.
-/

/-- If h ∈ ℤ[X] is intersective, then the shifted polynomial h(X + c) is also intersective for any integer c. -/
theorem is_intersective_comp_X_add_C (h : Polynomial ℤ) (hh : is_intersective h) (c : ℤ) :
    is_intersective (h.comp (Polynomial.X + Polynomial.C c)) := by
  intro m hm
  obtain ⟨n, hn⟩ := hh m hm
  use n - c
  rw [Polynomial.eval_comp]
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  rw [sub_add_cancel]
  exact hn
