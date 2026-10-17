import AFTD.Prelude
import AFTD.Kb.Tcs.ComplexLaplaceTransform
import AFTD.Kb.Tcs.ComplexLaplaceConvergenceDomain
import AFTD.Kb.Tcs.ContinuousAtComplexLaplaceTransformOfMemInteriorConvergenceDomain

/-!
# continuousOn_complexLaplaceTransform_interior_convergenceDomain

Topic: quantum   Node: 972ad41641f5

Provenance: formalization of a published result. Source: QuantumInfo, `continuousOn_complexLaplaceTransform_interior_convergenceDomain`. Lean proof by Dennj Osele, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/ComplexLaplaceTransform.lean (Copyright (c) 2025 Dennj Osele. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

continuousOn_complexLaplaceTransform_interior_convergenceDomain
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
theorem continuousOn_complexLaplaceTransform_interior_convergenceDomain
    {α : Type*} [MeasureTheory.MeasureSpace α] {E : α → WithTop ℝ} :
    ContinuousOn (ComplexLaplaceTransform E) (interior (ComplexLaplaceConvergenceDomain E)) := by
  intro z hz
  exact (continuousAt_complexLaplaceTransform_of_mem_interior_convergenceDomain hz).continuousWithinAt
