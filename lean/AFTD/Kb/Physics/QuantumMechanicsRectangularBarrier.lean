import AFTD.Prelude

/-!
# QuantumMechanics.RectangularBarrier

Topic: quantum_mechanics   Node: 341ed24f17eb

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.RectangularBarrier`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/RectangularBarrier/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A quantum particle with mass `m > 0` on `Space 1` subject to a rectangular potential barrier. The potential is `V₀` on the interval `Icc lower upper` and zero elsewhere.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Set MeasureTheory in
/-- A quantum particle with mass `m > 0` on `Space 1` subject to a rectangular potential barrier. The potential is `V₀` on the interval `Icc lower upper` and zero elsewhere. -/
structure QuantumMechanics.RectangularBarrier where
  /-- The mass (positive). -/
  m : ℝ
  hm : 0 < m
  /-- The lower bound of the barrier. -/
  lower : ℝ
  /-- The upper bound of the barrier. -/
  upper : ℝ
  h_bounds : lower < upper
  /-- The height of the potential barrier. -/
  V₀ : ℝ
