import AFTD.Prelude
import AFTD.Kb.Physics.RealCompleteEllipticKRadicandPos

/-!
# Real.continuous_completeEllipticK_integrand

Topic: classical_mechanics   Node: a8ebbaa16f13

Provenance: formalization of a published result. Source: Physlib, `Real.continuous_completeEllipticK_integrand`. Lean proof by Aadarsh Agarwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/SpecialFunctions/EllipticIntegral.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For `m < 1` the integrand of `completeEllipticK m` is continuous, the real power being taken at a positive base.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory in
/-- For `m < 1` the integrand of `completeEllipticK m` is continuous, the real power being taken at a positive base. -/
lemma Real.continuous_completeEllipticK_integrand {m : ℝ} (hm : m < 1) :
    Continuous fun φ : ℝ => (1 - m * sin φ ^ 2) ^ (-(1 / 2 : ℝ)) := by
  refine Continuous.rpow_const ?_ fun φ => Or.inl (completeEllipticK_radicand_pos hm φ).ne'
  fun_prop
