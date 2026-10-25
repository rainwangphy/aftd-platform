import AFTD.Prelude

/-!
# three_hadamard_clean_return_numerator

Topic: quantum   Node: 5eeef6e51692

Provenance: helper lemma. Supporting algebra for OP-3, arXiv:2610.01024, Section E.1; developed in deep session IN-184. These helpers do not establish a lower bound for arbitrary circuit gate lists.

The (1,0) entry of the unnormalized three-Hadamard, two-diagonal-phase chain is 1-u+v+u*v.
-/

theorem three_hadamard_clean_return_numerator (u v : ℂ) :
    ((!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℂ) *
      Matrix.diagonal ![1,u] * !![1,1;1,-1] *
      Matrix.diagonal ![1,v] * !![1,1;1,-1] : Matrix (Fin 2) (Fin 2) ℂ) 1 0 =
        1 - u + v + u*v := by
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  ring
