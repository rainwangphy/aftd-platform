import AFTD.Prelude
import AFTD.Kb.Tcs.IntCrescentPoint

/-!
# int_crescent_point_injective

Topic: combinatorics   Node: 09b5e3982bb0

Provenance: helper lemma. arXiv:2610.38368 Section 3

For every integer n ≥ 3, the function int_crescent_point n from Fin n to Fin 3 → ℤ is injective.
-/

/-- The indexing function int_crescent_point n is injective for n ≥ 3. -/
theorem int_crescent_point_injective (n : ℕ) (hn : 3 ≤ n) :
    Function.Injective (int_crescent_point n) := by
  intro j1 j2 h
  have h2 := congrFun h 2
  simp only [int_crescent_point] at h2
  have hP : (4 * (n : ℤ)^2 + 1) ^ (n - 1) ≠ 0 := by positivity
  have h2' : 2 * (j1 : ℤ) = 2 * (j2 : ℤ) := mul_right_cancel₀ hP h2
  have hz : (j1 : ℤ) = (j2 : ℤ) :=
    mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h2'
  have hval : j1.val = j2.val := by exact_mod_cast hz
  exact Fin.ext hval
