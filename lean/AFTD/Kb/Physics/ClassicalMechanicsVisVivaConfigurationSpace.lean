import AFTD.Prelude

/-!
# ClassicalMechanics.VisViva.ConfigurationSpace

Topic: classical_mechanics   Node: f0a142d50b3e

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.VisViva.ConfigurationSpace`. Lean proof by Hannah Dawe, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/OrbitalMechanics/VisViva.lean (Copyright (c) 2026 Hannah Dawe. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Configuration space for orbital mechanics, defining the orbital radius.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Configuration space for orbital mechanics, defining the orbital radius. -/
structure ClassicalMechanics.VisViva.ConfigurationSpace where
  /-- Orbital radius. -/
  r : ℝ
