import AFTD.Prelude

/-!
# three_qubit_skew_axis_plane_pair_symmetry

Topic: linear_algebra   Node: 5b9aaae4061d

Provenance: helper lemma.

If the cross product of two real vectors is perpendicular to the vector dual to the skew part of a real 3 by 3 matrix, the matrix pairs those vectors symmetrically. In particular this holds for vectors in any plane containing that skew vector.
-/

theorem three_qubit_skew_axis_plane_pair_symmetry
    (A : Matrix (Fin 3) (Fin 3) ℝ) (a b : Fin 3 → ℝ)
    (h : (A 2 1 - A 1 2)*(a 1*b 2-a 2*b 1) +
      (A 0 2 - A 2 0)*(a 2*b 0-a 0*b 2) +
      (A 1 0 - A 0 1)*(a 0*b 1-a 1*b 0) = 0) :
    (∑ i, ∑ j, a i * A i j * b j) = (∑ i, ∑ j, b i * A i j * a j) := by
  simp [Fin.sum_univ_succ]
  linear_combination -h
