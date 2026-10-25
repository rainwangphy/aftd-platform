import AFTD.Prelude

/-!
# binary_linear_lift_third_difference

Topic: quantum   Node: 3ffdaf34c5b1

Provenance: helper lemma. Supporting algebra for OP-3, arXiv:2610.01024, Section E.1; developed in deep session IN-184. These helpers do not establish a lower bound for arbitrary circuit gate lists.

The third alternating finite difference of a lifted binary linear form on a three-dimensional cube equals four times the product of its three coefficients modulo eight.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000

theorem binary_linear_lift_third_difference (l : Fin 3 → ZMod 2) :
    (∑ x : Fin 3 → ZMod 2,
      (-1 : ZMod 8) ^ (∑ i : Fin 3, (x i).val) *
        (((∑ i : Fin 3, l i*x i).val : ℕ) : ZMod 8)) =
      4 * (((l 0*l 1*l 2).val : ℕ) : ZMod 8) := by
  revert l
  decide
