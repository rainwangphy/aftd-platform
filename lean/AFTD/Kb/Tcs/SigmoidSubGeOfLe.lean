import AFTD.Prelude
import AFTD.Tactic.NumBounds
import AFTD.Kb.Physics.ProbabilisticTheoryOrderedVectorSpace
import AFTD.Kb.Physics.ProbabilisticTheoryInstArchimedeanOrderUnitSpaceReal
import AFTD.Kb.Physics.ProbabilisticTheoryOrderUnitSpace
import AFTD.Kb.Physics.ProbabilisticTheoryArchimedeanOrderUnitSpace

/-!
# sigmoid_sub_ge_of_le

Topic: circuits   Node: 9e0494630d3e

Provenance: helper lemma. scout/2611-21910-new-gate-weight-and-wire-complexity-bounds-for-sigmoid-neur.md:897

For any real numbers 0 ≤ u ≤ v ≤ 1, the difference sigmoid(v) - sigmoid(u) is at least (1/6) * (v - u).
-/

/-- Mean value lower bound for the standard sigmoid function on the interval [0, 1]. -/
theorem sigmoid_sub_ge_of_le (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1) :
    (1 / 6 : ℝ) * (v - u) ≤ Real.sigmoid v - Real.sigmoid u := by
  open Set Real in
  have hcvx : Convex ℝ (Icc (0:ℝ) 1) := convex_Icc 0 1
  have hcont : ContinuousOn sigmoid (Icc 0 1) := continuous_sigmoid.continuousOn
  have hdiff : DifferentiableOn ℝ sigmoid (interior (Icc 0 1)) :=
    differentiable_sigmoid.differentiableOn
  have h_one : (1 / 6 : ℝ) ≤ sigmoid 1 * (1 - sigmoid 1) := by
    unfold sigmoid
    num_ineq
  have hderiv : ∀ x ∈ interior (Icc (0:ℝ) 1), (1 / 6 : ℝ) ≤ deriv sigmoid x := by
    intro x hx
    have hx_icc : x ∈ Icc (0:ℝ) 1 := interior_subset hx
    have h0x : (0:ℝ) ≤ x := hx_icc.1
    have hx1 : x ≤ 1 := hx_icc.2
    have hsig0 : sigmoid 0 ≤ sigmoid x := sigmoid_le h0x
    have hsig1 : sigmoid x ≤ sigmoid 1 := sigmoid_le hx1
    rw [sigmoid_zero] at hsig0
    have h_quad : sigmoid 1 * (1 - sigmoid 1) ≤ sigmoid x * (1 - sigmoid x) := by
      have : (1 / 2 : ℝ) ≤ sigmoid x := by linarith [hsig0]
      nlinarith
    have hd : deriv sigmoid x = sigmoid x * (1 - sigmoid x) := by
      rw [deriv_sigmoid]
    rw [hd]
    linarith
  have hu_mem : u ∈ Icc (0:ℝ) 1 := ⟨hu, huv.trans hv⟩
  have hv_mem : v ∈ Icc (0:ℝ) 1 := ⟨hu.trans huv, hv⟩
  exact hcvx.mul_sub_le_image_sub_of_le_deriv hcont hdiff hderiv u hu_mem v hv_mem huv
