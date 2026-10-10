import AFTD.Prelude
import AFTD.Kb.Physics.ElectromagnetismFreeSpace
import AFTD.Kb.Physics.ElectromagnetismFreeSpaceEpsilon0Nonneg

/-!
# Electromagnetism.FreeSpace.μ₀_nonneg

Topic: classical_fields   Node: 1f74e5c24db3

Provenance: formalization of a published result. Source: Physlib, `Electromagnetism.FreeSpace.μ₀_nonneg`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Electromagnetism/Dynamics/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Electromagnetism.FreeSpace.μ₀_nonneg
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Electromagnetism in
variable (𝓕 : FreeSpace) in
@[simp]
lemma Electromagnetism.FreeSpace.μ₀_nonneg : 0 ≤ 𝓕.μ₀ := le_of_lt 𝓕.μ₀_pos
