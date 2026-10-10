import AFTD.Prelude
import AFTD.Kb.Physics.SpeedOfLight
import AFTD.Kb.Physics.SpeedOfLightValOne
import AFTD.Kb.Physics.SpeedOfLightValPos
import AFTD.Kb.Physics.SpeedOfLightValNonneg
import AFTD.Kb.Physics.SpeedOfLightInstCoeReal
import AFTD.Kb.Physics.SpeedOfLightInstOne

/-!
# SpeedOfLight.val_ne_zero

Topic: special_relativity   Node: 3dace47ddf94

Provenance: formalization of a published result. Source: Physlib, `SpeedOfLight.val_ne_zero`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/SpeedOfLight.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SpeedOfLight.val_ne_zero
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
@[simp]
lemma SpeedOfLight.val_ne_zero (c : SpeedOfLight) : (c : ℝ) ≠ 0 := ne_of_gt c.pos
