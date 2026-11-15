import AFTD.Prelude
import AFTD.Kb.Tcs.OseBooleanCubeDistSqHamming

/-!
# ose_boolean_cube_geometry

Topic: algorithms   Node: c31d114eae4b

Provenance: helper lemma. arXiv:2611.08546, Section 6.1, Boolean cube geometry

The standard Boolean cube in Euclidean space lies on the sphere about its center of squared radius n/4, and distinct vertices are separated by squared distance at least one.
-/

theorem ose_boolean_cube_geometry (n : ℕ) : (∀ x : Fin n → Bool, ‖(WithLp.toLp 2 (fun i : Fin n => if x i then (1 : ℝ) else 0) : EuclideanSpace ℝ (Fin n)) - (WithLp.toLp 2 (fun _ : Fin n => (1 : ℝ) / 2) : EuclideanSpace ℝ (Fin n))‖ ^ 2 = (n : ℝ) / 4) ∧ (∀ x y : Fin n → Bool, x ≠ y → 1 ≤ dist (WithLp.toLp 2 (fun i : Fin n => if x i then (1 : ℝ) else 0) : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 (fun i : Fin n => if y i then (1 : ℝ) else 0)) ^ 2) := by
  classical
  constructor
  · intro x
    rw [EuclideanSpace.norm_sq_eq]
    simp only [WithLp.ofLp_sub, WithLp.ofLp_toLp, Pi.sub_apply, Real.norm_eq_abs, sq_abs]
    have h (i : Fin n) : ((if x i then (1 : ℝ) else 0) - 1/2)^2 = 1/4 := by
      cases hx : x i <;> norm_num [hx]
    simp_rw [h]
    simp [div_eq_mul_inv]
  · intro x y hxy
    rw [ose_boolean_cube_dist_sq_hamming]
    have h : 1 ≤ hammingDist x y := Nat.one_le_iff_ne_zero.mpr (hammingDist_ne_zero.mpr hxy)
    exact_mod_cast h
