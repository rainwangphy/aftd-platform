import AFTD.Prelude
import AFTD.Kb.Physics.SpeedOfLight
import AFTD.Kb.Physics.SpeedOfLightInstOne
import AFTD.Kb.Physics.SpeedOfLightInstCoeReal

/-!
# SpeedOfLight.val_one

Topic: special_relativity   Node: 7096dd7d9598

Provenance: formalization of a published result. Source: Physlib, `SpeedOfLight.val_one`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/SpeedOfLight.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SpeedOfLight.val_one
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
@[simp]
lemma SpeedOfLight.val_one : (1 : SpeedOfLight).val = 1 := rfl
