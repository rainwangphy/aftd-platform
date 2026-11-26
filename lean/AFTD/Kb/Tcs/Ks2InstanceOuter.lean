import AFTD.Prelude
import AFTD.Kb.Tcs.Ks2InstanceVector

/-!
# ks2_instance_outer

Topic: np_completeness   Node: e1bb203ac372

Provenance: formalization of a published result. Source: arXiv:2611.27740, Problem 1.1: the outer product v v† of an input vector.

With explicit arguments d : ℕ and p : ℚ × List (ℚ × ℚ), in this order: the d×d complex matrix v v† (type Matrix (Fin d) (Fin d) ℂ), where v = ks2_instance_vector d p; that is Matrix.vecMulVec v (star v), whose (i, j) entry is v_i times the complex conjugate of v_j.
-/

/-- The rank-one term `v v†` of the encoded vector `v`. -/
noncomputable def ks2_instance_outer (d : ℕ) (p : ℚ × List (ℚ × ℚ)) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.vecMulVec (ks2_instance_vector d p) (star (ks2_instance_vector d p))
