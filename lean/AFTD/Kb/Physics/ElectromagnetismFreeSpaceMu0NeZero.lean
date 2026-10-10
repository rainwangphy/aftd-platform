import AFTD.Prelude
import AFTD.Kb.Physics.ElectromagnetismFreeSpace
import AFTD.Kb.Physics.ElectromagnetismFreeSpaceEpsilon0Nonneg
import AFTD.Kb.Physics.ElectromagnetismFreeSpaceMu0Nonneg
import AFTD.Kb.Physics.ElectromagnetismFreeSpaceEpsilon0NeZero

/-!
# Electromagnetism.FreeSpace.μ₀_ne_zero

Topic: classical_fields   Node: deb4333b6c88

Provenance: formalization of a published result. Source: Physlib, `Electromagnetism.FreeSpace.μ₀_ne_zero`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Electromagnetism/Dynamics/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Electromagnetism.FreeSpace.μ₀_ne_zero
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Electromagnetism in
variable (𝓕 : FreeSpace) in
@[simp]
lemma Electromagnetism.FreeSpace.μ₀_ne_zero : 𝓕.μ₀ ≠ 0 := ne_of_gt 𝓕.μ₀_pos
