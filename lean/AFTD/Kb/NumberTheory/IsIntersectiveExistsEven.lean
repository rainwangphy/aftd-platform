import AFTD.Prelude
import AFTD.Kb.NumberTheory.IsIntersective
import AFTD.Kb.NumberTheory.IsIntersectiveExistsPos

/-!
# is_intersective_exists_even

Topic: elementary_number_theory   Node: cc50e95044e6

Provenance: helper lemma. step towards op_153_subexp_bound_intersective_quadratic

Every intersective polynomial $h \in \mathbb{Z}[X]$ takes an even value at some positive natural number $n > 0$.
-/

/-- Every intersective polynomial h ∈ ℤ[X] takes an even value at some positive integer n > 0. -/
theorem is_intersective_exists_even (h : Polynomial ℤ) (hh : is_intersective h) :
    ∃ n : ℕ, 0 < n ∧ Even (h.eval (n : ℤ)) := by
  obtain ⟨n, hnpos, hnmod⟩ := is_intersective_exists_pos h hh 2 (by norm_num)
  exact ⟨n, hnpos, Int.even_iff.mpr hnmod⟩
