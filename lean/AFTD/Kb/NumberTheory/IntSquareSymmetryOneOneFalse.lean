import AFTD.Prelude
import AFTD.Kb.NumberTheory.IntSquareSymmetry

/-!
# int_square_symmetry_one_one_false

Topic: elementary_number_theory   Node: 7c82bbac3491

Provenance: helper lemma. Sanity lemma for the square symmetries, arXiv:2610.16562 (The Davenport constant of low-dimensional boxes).

The identity is among the eight square symmetries (signs +1, no swap).
-/

theorem int_square_symmetry_one_one_false (v : ℤ × ℤ) : int_square_symmetry 1 1 false v = v := by
  simp [int_square_symmetry]
