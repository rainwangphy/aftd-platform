import AFTD.Prelude

/-!
# matrix_order_four_centered_shift

Topic: graphs   Node: 4fea6c6cd6af

Provenance: helper lemma. Sector-bound formalization for IN-166; arXiv:math/0508176, Theorem 5.

Add a scalar multiple of the identity minus the averaging matrix to an order-four real matrix.
-/

noncomputable def matrix_order_four_centered_shift (L : Matrix (Fin 4) (Fin 4) ℝ) (b : ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ := fun i j => L i j + (if i = j then b else 0) - b / 4
