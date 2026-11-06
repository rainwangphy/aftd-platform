import AFTD.Prelude
import AFTD.Kb.Optimization.CubeFunc
import AFTD.Kb.Optimization.IsSubmodularCube

/-!
# all_cube_func_one_is_submodular

Topic: submodular   Node: dd7b32d5e8d5

Provenance: helper lemma. arXiv:2611.02374, Sec. 2

On the 1-dimensional Boolean hypercube, every function f : {0, 1}^1 → {0, ..., k} is submodular.
-/

/-- Every function on the 1-dimensional Boolean hypercube is submodular. -/
theorem all_cube_func_one_is_submodular (k : ℕ) (f : CubeFunc 1 k) :
    is_submodular_cube f := by
  intro x y
  rcases le_total (x 0) (y 0) with h | h
  · have hle : x ≤ y := by
      intro i
      rw [Subsingleton.elim i 0]
      exact h
    rw [sup_eq_right.mpr hle, inf_eq_left.mpr hle]
    linarith
  · have hle : y ≤ x := by
      intro i
      rw [Subsingleton.elim i 0]
      exact h
    rw [sup_eq_left.mpr hle, inf_eq_right.mpr hle]
