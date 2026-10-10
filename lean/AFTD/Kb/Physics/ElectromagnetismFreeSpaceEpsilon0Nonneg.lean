import AFTD.Prelude
import AFTD.Kb.Physics.ElectromagnetismFreeSpace

/-!
# Electromagnetism.FreeSpace.ε₀_nonneg

Topic: classical_fields   Node: eaf7067ed3c8

Provenance: formalization of a published result. Source: Physlib, `Electromagnetism.FreeSpace.ε₀_nonneg`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Electromagnetism/Dynamics/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Electromagnetism.FreeSpace.ε₀_nonneg
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Electromagnetism in
variable (𝓕 : FreeSpace) in
@[simp]
lemma Electromagnetism.FreeSpace.ε₀_nonneg : 0 ≤ 𝓕.ε₀ := le_of_lt 𝓕.ε₀_pos
