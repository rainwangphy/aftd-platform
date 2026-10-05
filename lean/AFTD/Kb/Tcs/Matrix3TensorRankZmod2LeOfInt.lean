import AFTD.Prelude
import AFTD.Kb.Tcs.Matrix3TensorRankLeOfSurjective
import AFTD.Kb.Tcs.Matrix3TensorRankLe

/-!
# matrix3_tensor_rank_zmod2_le_of_int

Topic: algebraic_complexity   Node: 1ca96da3d77c

A bilinear algorithm for 3x3 matrix multiplication with integer coefficients and r products gives one over the two-element field with r products; in particular a 22-product algorithm over the integers would answer the two-element-field question positively.
-/

theorem matrix3_tensor_rank_zmod2_le_of_int (r : ℕ) (h : matrix3_tensor_rank_le ℤ r) : matrix3_tensor_rank_le (ZMod 2) r := matrix3_tensor_rank_le_of_surjective (Int.castRingHom (ZMod 2)) ZMod.intCast_surjective r h
