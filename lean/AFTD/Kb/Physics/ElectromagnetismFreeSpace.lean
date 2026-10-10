import AFTD.Prelude

/-!
# Electromagnetism.FreeSpace

Topic: classical_fields   Node: 062030178193

Provenance: formalization of a published result. Source: Physlib, `Electromagnetism.FreeSpace`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Electromagnetism/Dynamics/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Free space consists of the specification of the electric permittivity and the magnetic permeability.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Free space consists of the specification of the electric permittivity and the magnetic permeability. -/
structure Electromagnetism.FreeSpace where
  /-- The permittivity. -/
  ε₀ : ℝ
  /-- The permeability. -/
  μ₀ : ℝ
  ε₀_pos : 0 < ε₀
  μ₀_pos : 0 < μ₀
