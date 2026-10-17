import AFTD.Prelude
import AFTD.Kb.Tcs.ComplexLaplaceConvergenceDomain
import AFTD.Kb.Tcs.ComplexLaplaceTransform
import AFTD.Kb.Tcs.ComplexLaplaceIntegrand
import AFTD.Kb.Tcs.ComplexLaplaceEnvelope
import AFTD.Kb.Tcs.EventuallyIntegrableComplexLaplaceIntegrandOfMemInteriorConvergenceDomain
import AFTD.Kb.Tcs.NormComplexLaplaceIntegrandLeEnvelope
import AFTD.Kb.Tcs.AnalyticAtComplexLaplaceIntegrand

/-!
# continuousAt_complexLaplaceTransform_of_mem_interior_convergenceDomain

Topic: quantum   Node: 24344c77857e

Provenance: formalization of a published result. Source: QuantumInfo, `continuousAt_complexLaplaceTransform_of_mem_interior_convergenceDomain`. Lean proof by Dennj Osele, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/ComplexLaplaceTransform.lean (Copyright (c) 2025 Dennj Osele. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

continuousAt_complexLaplaceTransform_of_mem_interior_convergenceDomain
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
theorem continuousAt_complexLaplaceTransform_of_mem_interior_convergenceDomain
    {α : Type*} [MeasureTheory.MeasureSpace α] {E : α → WithTop ℝ} {z : ℂ}
    (hz : z ∈ interior (ComplexLaplaceConvergenceDomain E)) :
    ContinuousAt (ComplexLaplaceTransform E) z := by
  rcases Metric.isOpen_iff.mp isOpen_interior z hz with ⟨ε, hε_pos, hε⟩
  have hint {w : ℂ} (hw : w ∈ Metric.ball z ε) :
      MeasureTheory.Integrable (μ := MeasureTheory.volume) (ComplexLaplaceIntegrand E w) :=
    _root_.interior_subset (s := ComplexLaplaceConvergenceDomain E) (hε hw)
  have hbound_int : MeasureTheory.Integrable (μ := MeasureTheory.volume)
      (ComplexLaplaceEnvelope E z (ε / 2)) := by
    unfold ComplexLaplaceEnvelope
    exact (hint (by
      rw [Metric.mem_ball, dist_eq_norm]
      simpa [abs_of_pos hε_pos] using show ε / 2 < ε by linarith)).norm.add (hint (by
        rw [Metric.mem_ball, dist_eq_norm]
        simpa [abs_of_pos hε_pos] using show ε / 2 < ε by linarith)).norm
  exact
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := MeasureTheory.volume) (l := nhds z)
      (F := fun w x => ComplexLaplaceIntegrand E w x)
      (f := fun x => ComplexLaplaceIntegrand E z x)
      (ComplexLaplaceEnvelope E z (ε / 2))
      ((eventually_integrable_complexLaplaceIntegrand_of_mem_interior_convergenceDomain (E := E) hz).mono
        fun _ hw => hw.aestronglyMeasurable)
      (Filter.Eventually.mono (Metric.ball_mem_nhds z (by positivity : 0 < ε / 2)) fun w hw =>
        Filter.Eventually.of_forall fun x => norm_complexLaplaceIntegrand_le_envelope
          (Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hw))) x)
      hbound_int
      (Filter.Eventually.of_forall fun x => (analyticAt_complexLaplaceIntegrand E x z).continuousAt)
