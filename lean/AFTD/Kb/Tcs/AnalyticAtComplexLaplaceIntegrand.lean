import AFTD.Prelude
import AFTD.Kb.Tcs.ComplexLaplaceIntegrand

/-!
# analyticAt_complexLaplaceIntegrand

Topic: quantum   Node: c17acae5c0b5

Provenance: formalization of a published result. Source: QuantumInfo, `analyticAt_complexLaplaceIntegrand`. Lean proof by Dennj Osele, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/ComplexLaplaceTransform.lean (Copyright (c) 2025 Dennj Osele. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For each configuration, the complex Laplace integrand is analytic in the parameter.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- For each configuration, the complex Laplace integrand is analytic in the parameter. -/
theorem analyticAt_complexLaplaceIntegrand
    {α : Type*} (E : α → WithTop ℝ) (x : α) (z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => ComplexLaplaceIntegrand E w x) z := by
  unfold ComplexLaplaceIntegrand
  split_ifs
  · fun_prop
  · fun_prop
