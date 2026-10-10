import AFTD.Prelude

/-!
# Real.completeEllipticK_radicand_pos

Topic: classical_mechanics   Node: 6bfd3fc6d1ff

Provenance: formalization of a published result. Source: Physlib, `Real.completeEllipticK_radicand_pos`. Lean proof by Aadarsh Agarwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/SpecialFunctions/EllipticIntegral.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For `m < 1` the radicand `1 - m sin² φ` of the integrand of `completeEllipticK m` is positive at every angle `φ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory in
/-- For `m < 1` the radicand `1 - m sin² φ` of the integrand of `completeEllipticK m` is positive at every angle `φ`. -/
lemma Real.completeEllipticK_radicand_pos {m : ℝ} (hm : m < 1) (φ : ℝ) :
    0 < 1 - m * sin φ ^ 2 := by
  nlinarith [sq_nonneg (sin φ), sin_sq_le_one φ,
    mul_nonneg (sub_nonneg.2 hm.le) (sq_nonneg (sin φ))]
