import AFTD.Prelude

/-!
# QuantumMechanics.PoschlTeller

Topic: quantum_mechanics   Node: 904707fbff93

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.PoschlTeller`. Lean proof by Afiq Hatta, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/PoschlTeller/Basic.lean (Copyright (c) 2025 Afiq Hatta. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A Pöschl-Teller system is specified by the particle mass `m`, the width parameter `κ`, and family number `N` (all positive). -
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Complex Real SchwartzMap MeasureTheory in
/-- A Pöschl-Teller system is specified by the particle mass `m`, the width parameter `κ`, and family number `N` (all positive). - -/
structure QuantumMechanics.PoschlTeller where
  /-- mass of the particle -/
  m : ℝ
  /-- width parameter of the potential -/
  κ : ℝ
  /-- family number, positive integer -/
  N : ℕ
  m_pos : 0 < m -- mass of the particle is positive
  κ_pos : 0 < κ -- width parameter of the potential is positive
  N_pos : 0 < N -- family number is positive
