import AFTD.Prelude

/-!
# three_qubit_canonical_pair_correlation_cycle_symmetric

Topic: quantum   Node: 640361a14893

Provenance: helper lemma. arXiv:2611.19367v1, Appendix A, Eqs. (A1)–(A5); the matrices and their symmetry are stated there.

For the three explicit real correlation matrices obtained from the six-parameter three-qubit canonical form, the matrix Bᵀ adj(A)ᵀ C is symmetric for all real parameters, without invertibility or normalization assumptions.
-/

open scoped Matrix

theorem three_qubit_canonical_pair_correlation_cycle_symmetric (l u v p q r : ℝ) :
  let A : Matrix (Fin 3) (Fin 3) ℝ :=
    !![2*q*l, 0, 2*u*l; 0, -2*q*l, 2*v*l;
       -2*u*q-2*p*r, 2*v*q, -u^2-v^2-p^2+q^2+r^2+l^2]
  let B : Matrix (Fin 3) (Fin 3) ℝ :=
    !![2*p*l, 0, 2*u*l; 0, -2*p*l, 2*v*l;
       -2*u*p-2*q*r, 2*v*p, -u^2-v^2+p^2-q^2+r^2+l^2]
  let C : Matrix (Fin 3) (Fin 3) ℝ :=
    !![2*u*r+2*p*q, -2*v*r, 2*u*q-2*p*r;
       -2*v*r, -2*u*r+2*p*q, -2*v*q;
       2*u*p-2*q*r, -2*v*p, u^2+v^2-p^2-q^2+r^2+l^2]
  let K := B.transpose * A.adjugate.transpose * C
  K.transpose = K := by
  dsimp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.adjugate_fin_three, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.cons_val_three] <;> ring
