import AFTD.Prelude
import AFTD.Kb.Tcs.Matrix3TensorRankGeOfSurjective
import AFTD.Kb.Tcs.Matrix3TensorRankGe

/-!
# matrix3_tensor_rank_int_ge_of_zmod2

Topic: algebraic_complexity   Node: 0eb8bdedf1bd

Provenance: formalization of a published result. Source: Lower Bound of 22 for 3x3 Matrix Multiplication over the Integers, arXiv:2610.01639, Sec. 5.3 (lower bounds over the two-element field bound algorithms with integer constants)

A lower bound r on the number of products of every bilinear algorithm for 3x3 matrix multiplication over the two-element field is also a lower bound over the integers.
-/

theorem matrix3_tensor_rank_int_ge_of_zmod2 (r : ℕ) (h : matrix3_tensor_rank_ge (ZMod 2) r) : matrix3_tensor_rank_ge ℤ r := matrix3_tensor_rank_ge_of_surjective (Int.castRingHom (ZMod 2)) ZMod.intCast_surjective r h
