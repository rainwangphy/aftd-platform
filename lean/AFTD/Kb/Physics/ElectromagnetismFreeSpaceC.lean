import AFTD.Prelude
import AFTD.Kb.Physics.ElectromagnetismFreeSpace
import AFTD.Kb.Physics.SpeedOfLight
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
# Electromagnetism.FreeSpace.c

Topic: classical_fields   Node: 14db7cdaec03

Provenance: formalization of a published result. Source: Physlib, `Electromagnetism.FreeSpace.c`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Electromagnetism/Dynamics/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The speed of light in free space.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Electromagnetism in
variable (𝓕 : FreeSpace) in
/-- The speed of light in free space. -/
noncomputable def Electromagnetism.FreeSpace.c : SpeedOfLight :=
  ⟨1 / √(𝓕.ε₀ * 𝓕.μ₀), by
    apply div_pos
    · exact zero_lt_one
    · refine Real.sqrt_pos_of_pos ?_
      apply mul_pos 𝓕.ε₀_pos 𝓕.μ₀_pos⟩
