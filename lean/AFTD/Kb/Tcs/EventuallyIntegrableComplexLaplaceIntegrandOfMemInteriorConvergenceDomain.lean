import AFTD.Prelude
import AFTD.Kb.Tcs.ComplexLaplaceConvergenceDomain
import AFTD.Kb.Tcs.ComplexLaplaceIntegrand

/-!
# eventually_integrable_complexLaplaceIntegrand_of_mem_interior_convergenceDomain

Topic: quantum   Node: 67e33d7c177e

Provenance: formalization of a published result. Source: QuantumInfo, `eventually_integrable_complexLaplaceIntegrand_of_mem_interior_convergenceDomain`. Lean proof by Dennj Osele, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/ComplexLaplaceTransform.lean (Copyright (c) 2025 Dennj Osele. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Interior convergence gives integrability throughout a neighborhood of the parameter.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Interior convergence gives integrability throughout a neighborhood of the parameter. -/
theorem eventually_integrable_complexLaplaceIntegrand_of_mem_interior_convergenceDomain
    {α : Type*} [MeasureTheory.MeasureSpace α] {E : α → WithTop ℝ} {z : ℂ}
    (hz : z ∈ interior (ComplexLaplaceConvergenceDomain E)) :
    ∀ᶠ w in nhds z,
      MeasureTheory.Integrable (μ := MeasureTheory.volume) (ComplexLaplaceIntegrand E w) :=
  Filter.mem_of_superset (IsOpen.mem_nhds isOpen_interior hz) _root_.interior_subset
