import AFTD.Prelude

/-!
# binary_affine_lift_fourth_difference

Topic: quantum   Node: 35e696991181

Provenance: helper lemma. Supporting algebra for OP-3, arXiv:2610.01024, Section E.1; developed in deep session IN-184. These helpers do not establish a lower bound for arbitrary circuit gate lists.

The fourth alternating finite difference of the lift to Z/8 of any affine binary function on a four-dimensional cube is zero.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000

theorem binary_affine_lift_fourth_difference
    (a : ZMod 2) (l : Fin 4 → ZMod 2) :
    (∑ x : Fin 4 → ZMod 2,
      (-1 : ZMod 8) ^ (∑ i : Fin 4, (x i).val) *
        (((a + ∑ i : Fin 4, l i * x i).val : ℕ) : ZMod 8)) = 0 := by
  revert a l
  decide
