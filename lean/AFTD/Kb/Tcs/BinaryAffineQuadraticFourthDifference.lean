import AFTD.Prelude

/-!
# binary_affine_quadratic_fourth_difference

Topic: quantum   Node: b8ecf339b718

Provenance: helper lemma. Supporting algebra for OP-3, arXiv:2610.01024, Section E.1; developed in deep session IN-184. These helpers do not establish a lower bound for arbitrary circuit gate lists.

The fourth alternating difference of twice the lift of a four-variable binary quadratic, with arbitrary affine terms, is four times a*f+b*e+c*d, where a,b,c,d,e,f are its six quadratic coefficients.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000

theorem binary_affine_quadratic_fourth_difference
    (a b c d e f t : ZMod 2) (l : Fin 4 → ZMod 2) :
    (∑ x : Fin 4 → ZMod 2,
      (-1 : ZMod 8) ^ (∑ i : Fin 4, (x i).val) *
        (2 * (((a*x 0*x 1 + b*x 0*x 2 + c*x 0*x 3 +
          d*x 1*x 2 + e*x 1*x 3 + f*x 2*x 3 + t +
          ∑ i : Fin 4, l i*x i).val : ℕ) : ZMod 8))) =
      4 * (((a*f + b*e + c*d).val : ℕ) : ZMod 8) := by
  revert a b c d e f t l
  decide
