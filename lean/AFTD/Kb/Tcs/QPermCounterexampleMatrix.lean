import AFTD.Prelude

/-!
# q_perm_counterexample_matrix

Topic: combinatorics   Node: 2bcd439a8dbc

Provenance: formalization of a published result. Source: arXiv:2611.14694, Theorem 2.1

The 5-by-5 integer matrix with diagonal (5, 5, 1, 5, 5) and nonzero off-diagonal entries A_{0,3} = A_{3,0} = 4, A_{0,4} = A_{4,0} = 1, A_{1,3} = A_{3,1} = -1, and A_{1,4} = A_{4,1} = 4.
-/

/-- The 5x5 integer matrix from arXiv:2611.14694 Theorem 2.1 that disproves q-permanent monotonicity. -/
def q_perm_counterexample_matrix : Matrix (Fin 5) (Fin 5) ℤ :=
  !![ 5,  0, 0,  4, 1;
      0,  5, 0, -1, 4;
      0,  0, 1,  0, 0;
      4, -1, 0,  5, 0;
      1,  4, 0,  0, 5]
