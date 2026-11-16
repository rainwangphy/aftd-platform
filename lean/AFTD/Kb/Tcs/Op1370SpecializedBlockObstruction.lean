import AFTD.Prelude

/-!
# op1370_specialized_block_obstruction

Topic: combinatorics   Node: 88e501d5460d

Provenance: helper lemma. An algebraic obstruction found in experiment 28768 for OP-1370.

For arbitrary rational u and v, the determinant of the matrix with rows (2,1-u,1-v), (-1,u-1,0), and (-1,0,v-1) is zero.
-/

theorem op1370_specialized_block_obstruction (u v : ℚ) :
    Matrix.det (!![2, 1-u, 1-v; -1, u-1, 0; -1, 0, v-1] : Matrix (Fin 3) (Fin 3) ℚ) = 0 := by
  open Finset in
  rw [Matrix.det_fin_three]
  simp
  ring
