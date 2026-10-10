import AFTD.Prelude

/-!
# MassUnit

Topic: classical_mechanics   Node: ef362fdab4b2

Provenance: formalization of a published result. Source: Physlib, `MassUnit`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Mass/MassUnit.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The choices of translationally-invariant metrics on the mass-manifold. Such a choice corresponds to a choice of units for mass.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
/-- The choices of translationally-invariant metrics on the mass-manifold. Such a choice corresponds to a choice of units for mass. -/
structure MassUnit where
  /-- The underlying scale of the unit. -/
  val : ℝ
  property : 0 < val
