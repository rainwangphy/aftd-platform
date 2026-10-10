import AFTD.Prelude
import AFTD.Kb.Physics.ElectromagnetismFreeSpace
import AFTD.Kb.Physics.SpeedOfLight
import AFTD.Kb.Physics.ElectromagnetismFreeSpaceC
import AFTD.Kb.Physics.SpeedOfLightValOne
import AFTD.Kb.Physics.SpeedOfLightValPos
import AFTD.Kb.Physics.SpeedOfLightValNonneg
import AFTD.Kb.Physics.SpeedOfLightValNeZero
import AFTD.Kb.Physics.ElectromagnetismFreeSpaceEpsilon0Nonneg
import AFTD.Kb.Physics.ElectromagnetismFreeSpaceMu0Nonneg
import AFTD.Kb.Physics.ElectromagnetismFreeSpaceEpsilon0NeZero
import AFTD.Kb.Physics.ElectromagnetismFreeSpaceMu0NeZero
import AFTD.Kb.Physics.SpeedOfLightInstCoeReal
import AFTD.Kb.Physics.SpeedOfLightInstOne

/-!
# Electromagnetism.FreeSpace.c_val

Topic: classical_fields   Node: ff26dcfa73a8

Provenance: formalization of a published result. Source: Physlib, `Electromagnetism.FreeSpace.c_val`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Electromagnetism/Dynamics/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Electromagnetism.FreeSpace.c_val
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Electromagnetism Electromagnetism.FreeSpace in
variable (𝓕 : FreeSpace) in
lemma Electromagnetism.FreeSpace.c_val : (𝓕.c : ℝ) = 1 / √(𝓕.ε₀ * 𝓕.μ₀) := rfl
