import AFTD.Prelude
import AFTD.Kb.Tcs.Matrix3Triad
import AFTD.Kb.Tcs.EvalMatrix3Decomposition

/-!
# matrix3_unit_check

Topic: algebraic_complexity   Node: e038eaa83f4f

Provenance: helper lemma. step towards matrix3_tensor_rank_zmod2_le_22

A computable Bool-valued checker that tests a list L of triads over ZMod 2 against all 81 pairs of 3x3 matrix units: it returns true exactly when, for every i j k l : Fin 3, the evaluation of L at the unit pair (single i j 1, single k l 1) equals the product of those units.
-/

/-- Computable mirror of is_valid_matrix3_decomposition over ZMod 2: checks the list against the 81 matrix-unit pairs, i.e. 729 kernel-decidable identities. -/
def matrix3_unit_check (L : List (Matrix3Triad (ZMod 2))) : Bool := (List.finRange 3).all fun i =>
  (List.finRange 3).all fun j =>
  (List.finRange 3).all fun k =>
  (List.finRange 3).all fun l =>
    decide (eval_matrix3_decomposition L (Matrix.single i j (1 : ZMod 2)) (Matrix.single k l (1 : ZMod 2))
      = Matrix.single i j (1 : ZMod 2) * Matrix.single k l (1 : ZMod 2))
