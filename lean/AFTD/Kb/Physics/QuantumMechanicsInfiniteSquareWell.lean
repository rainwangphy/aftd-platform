import AFTD.Prelude

/-!
# QuantumMechanics.InfiniteSquareWell

Topic: quantum_mechanics   Node: 984bf55813aa

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.InfiniteSquareWell`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/InfiniteSquareWell/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A spinless quantum particle with mass `m > 0` confined to a cuboid in `Space d`. The bounds of the well are specified by two functions `lower upper : Fin d → ℝ` satisfying `∀ i, lower i < upper i`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Set MeasureTheory in
/-- A spinless quantum particle with mass `m > 0` confined to a cuboid in `Space d`. The bounds of the well are specified by two functions `lower upper : Fin d → ℝ` satisfying `∀ i, lower i < upper i`. -/
structure QuantumMechanics.InfiniteSquareWell (d : ℕ) where
  /-- The mass (positive). -/
  m : ℝ
  hm : 0 < m
  /-- The lower bounds of the well. -/
  lower : Fin d → ℝ
  /-- The upper bounds of the well. -/
  upper : Fin d → ℝ
  /-- The well is a non-empty set. -/
  h_bounds : ∀ i, lower i < upper i
