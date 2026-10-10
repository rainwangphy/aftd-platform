import AFTD.Prelude
import AFTD.Kb.Physics.SpeedOfLight
import AFTD.Kb.Physics.SpeedOfLightValOne
import AFTD.Kb.Physics.SpeedOfLightInstCoeReal
import AFTD.Kb.Physics.SpeedOfLightInstOne

/-!
# SpeedOfLight.val_pos

Topic: special_relativity   Node: e3778233e891

Provenance: formalization of a published result. Source: Physlib, `SpeedOfLight.val_pos`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/SpeedOfLight.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SpeedOfLight.val_pos
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
@[simp]
lemma SpeedOfLight.val_pos (c : SpeedOfLight) : 0 < (c : ℝ) := c.pos
