import AFTD.Prelude
import AFTD.Kb.Tcs.QuaternionBlochRotation
import AFTD.Kb.Tcs.QuaternionBlochRotationOrthogonal

/-!
# invertible_quaternion_axis_normalization

Topic: quantum   Node: 5ef1b25a0612

Provenance: helper lemma. arXiv:2611.19367v1, Lemma 3, normalized axes in Eq. (26).

A unit quaternion has unit rotation columns, and an invertible real linear image of such a column can be normalized to a unit vector.
-/

theorem invertible_quaternion_axis_normalization (L : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) (q : Fin 4 → ℝ) (hL : L.det ≠ 0) (hq : (∑ k, (q k)^2) = 1) : let r : Fin 3 → ℝ := fun k => quaternion_bloch_rotation q k i; let x := L.mulVec r; let d := Real.sqrt (∑ k, (x k)^2); (∑ k, (r k)^2) = 1 ∧ 0 < d ∧ (∑ k, (x k / d)^2) = 1 := by
  set r : Fin 3 → ℝ := fun k => quaternion_bloch_rotation q k i with hrdef
  set x : Fin 3 → ℝ := L.mulVec r with hxdef
  set d : ℝ := Real.sqrt (∑ k, (x k)^2) with hddef
  change (∑ k, (r k)^2) = 1 ∧ 0 < d ∧ (∑ k, (x k / d)^2) = 1
  have hr : ∑ k, (r k)^2 = 1 := by
    rw [hrdef]
    have horth := (quaternion_bloch_rotation_orthogonal q hq).1
    have h := congrFun (congrFun horth i) i
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at h
    simpa [pow_two] using h
  have hrne : r ≠ 0 := by
    intro h
    rw [h] at hr
    simp at hr
  have hxne : x ≠ 0 := by
    intro h
    have hmv : L.mulVec r = L.mulVec 0 := by rw [← hxdef, h]; simp
    exact hrne (Matrix.mulVec_injective_of_det_ne_zero hL hmv)
  have hSpos : 0 < ∑ k, (x k)^2 := by
    have hxex : ∃ k, x k ≠ 0 := by
      by_contra h
      push Not at h
      exact hxne (funext h)
    obtain ⟨k, hk⟩ := hxex
    have hkpos : 0 < (x k)^2 := sq_pos_of_ne_zero hk
    have hle : (x k)^2 ≤ ∑ j, (x j)^2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ k)
    linarith
  have hdpos : 0 < d := by
    rw [hddef, Real.sqrt_pos]
    exact hSpos
  refine ⟨hr, hdpos, ?_⟩
  have hd2 : d ^ 2 = ∑ k, (x k)^2 := by
    rw [hddef]
    exact Real.sq_sqrt hSpos.le
  simp only [div_pow]
  rw [← Finset.sum_div, ← hd2, div_self (pow_ne_zero 2 (ne_of_gt hdpos))]
