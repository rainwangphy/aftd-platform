import AFTD.Prelude
import AFTD.Kb.Tcs.ComplexLaplaceConvergenceDomain
import AFTD.Kb.Tcs.ComplexLaplaceTransform
import AFTD.Kb.Tcs.ComplexLaplaceIntegrand
import AFTD.Kb.Tcs.WedgeIntegralComplexLaplaceTransformEqIntegral
import AFTD.Kb.Tcs.AnalyticAtComplexLaplaceIntegrand
import AFTD.Kb.Tcs.ContinuousOnComplexLaplaceTransformInteriorConvergenceDomain

/-!
# analyticAt_complexLaplaceTransform_of_mem_interior_convergenceDomain

Topic: quantum   Node: c9d5ed9492e4

Provenance: formalization of a published result. Source: QuantumInfo, `analyticAt_complexLaplaceTransform_of_mem_interior_convergenceDomain`. Lean proof by Dennj Osele, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/ComplexLaplaceTransform.lean (Copyright (c) 2025 Dennj Osele. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A complex Laplace transform is analytic on the interior of its convergence domain.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A complex Laplace transform is analytic on the interior of its convergence domain. -/
theorem analyticAt_complexLaplaceTransform_of_mem_interior_convergenceDomain
    {α : Type*} [MeasureTheory.MeasureSpace α]
    [MeasureTheory.SFinite (MeasureTheory.volume : MeasureTheory.Measure α)] {E : α → WithTop ℝ} {z : ℂ}
    (hE : Measurable E)
    (hz : z ∈ interior (ComplexLaplaceConvergenceDomain E)) :
    AnalyticAt ℂ (ComplexLaplaceTransform E) z := by
  rcases Metric.isOpen_iff.mp isOpen_interior z hz with ⟨r, hr_pos, hr⟩
  have hcons : Complex.IsConservativeOn (ComplexLaplaceTransform E) (Metric.ball z r) := by
    intro a b hab
    rw [wedgeIntegral_complexLaplaceTransform_eq_integral hE (hab.trans hr),
      wedgeIntegral_complexLaplaceTransform_eq_integral hE (by
        simpa [Complex.Rectangle, Set.uIcc_comm] using hab.trans hr)]
    · rw [← MeasureTheory.integral_neg]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      exact (DifferentiableOn.isConservativeOn
        (fun y _hy => (analyticAt_complexLaplaceIntegrand E x y).differentiableAt.differentiableWithinAt))
        a b (Set.subset_univ _)
  exact ((Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn Metric.isOpen_ball).1
    ⟨hcons, continuousOn_complexLaplaceTransform_interior_convergenceDomain.mono hr⟩).analyticAt
      (Metric.ball_mem_nhds z hr_pos)
