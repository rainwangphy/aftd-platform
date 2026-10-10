import AFTD.Prelude

/-!
# ClassicalMechanics.VisViva

Topic: classical_mechanics   Node: 0ae1c9ff55f9

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.VisViva`. Lean proof by Hannah Dawe, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/OrbitalMechanics/VisViva.lean (Copyright (c) 2026 Hannah Dawe. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

System parameters for the vis-viva equation in circular orbital mechanics.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- System parameters for the vis-viva equation in circular orbital mechanics. -/
structure ClassicalMechanics.VisViva where
  /-- Gravitational constant. -/
  G : ℝ
  /-- Central mass body. -/
  M : ℝ
  /-- Orbiting mass body. -/
  m : ℝ
