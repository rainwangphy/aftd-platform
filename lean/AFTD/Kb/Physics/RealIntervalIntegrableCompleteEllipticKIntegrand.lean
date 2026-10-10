import AFTD.Prelude
import AFTD.Kb.Physics.RealContinuousCompleteEllipticKIntegrand

/-!
# Real.intervalIntegrable_completeEllipticK_integrand

Topic: classical_mechanics   Node: 452d22247e48

Provenance: formalization of a published result. Source: Physlib, `Real.intervalIntegrable_completeEllipticK_integrand`. Lean proof by Aadarsh Agarwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/SpecialFunctions/EllipticIntegral.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For `m < 1` the integrand of `completeEllipticK m` is interval integrable on `[0, π/2]`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory in
/-- For `m < 1` the integrand of `completeEllipticK m` is interval integrable on `[0, π/2]`. -/
lemma Real.intervalIntegrable_completeEllipticK_integrand {m : ℝ} (hm : m < 1) :
    IntervalIntegrable (fun φ : ℝ => (1 - m * sin φ ^ 2) ^ (-(1 / 2 : ℝ))) volume 0 (π / 2) :=
  (continuous_completeEllipticK_integrand hm).intervalIntegrable 0 (π / 2)
