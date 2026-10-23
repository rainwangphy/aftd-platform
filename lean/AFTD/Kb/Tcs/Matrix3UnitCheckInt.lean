import AFTD.Prelude
import AFTD.Kb.Tcs.Matrix3Triad
import AFTD.Kb.Tcs.EvalMatrix3Decomposition

/-!
# matrix3_unit_check_int

Topic: algebraic_complexity   Node: 863de0e21732

Provenance: helper lemma. step towards matrix3_tensor_rank_int_le_22

A computable Bool-valued checker that tests a list L of triads over ℤ against all 81 pairs of 3x3 matrix units: it returns true exactly when, for every i j k l : Fin 3, the evaluation of L at the unit pair equals the product of those units.
-/

/-- Computable Bool checker testing a list of integer triads on all 81 matrix unit pairs. -/
def matrix3_unit_check_int (L : List (Matrix3Triad ℤ)) : Bool := (List.finRange 3).all fun i =>
  (List.finRange 3).all fun j =>
  (List.finRange 3).all fun k =>
  (List.finRange 3).all fun l =>
    decide (eval_matrix3_decomposition L (Matrix.single i j (1 : ℤ)) (Matrix.single k l (1 : ℤ))
      = Matrix.single i j (1 : ℤ) * Matrix.single k l (1 : ℤ))
