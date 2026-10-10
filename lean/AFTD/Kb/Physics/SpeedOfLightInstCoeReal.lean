import AFTD.Prelude
import AFTD.Kb.Physics.SpeedOfLight

/-!
# SpeedOfLight.instCoeReal

Topic: special_relativity   Node: 0d0eaaabf8af

Provenance: formalization of a published result. Source: Physlib, `SpeedOfLight.instCoeReal`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/SpeedOfLight.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SpeedOfLight.instCoeReal
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
instance SpeedOfLight.instCoeReal : Coe SpeedOfLight ℝ := ⟨SpeedOfLight.val⟩
