import AFTD.Prelude
import AFTD.Kb.Physics.Time
import AFTD.Kb.Physics.TimeInstVAddReal
import AFTD.Kb.Physics.TimeInstNonempty

/-!
# Time.vadd_val

Topic: classical_mechanics   Node: 863518e216ac

Provenance: formalization of a published result. Source: Physlib, `Time.vadd_val`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Time/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Time.vadd_val
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped Manifold ContDiff in
@[simp]
lemma Time.vadd_val (dt : ℝ) (t : Time) : (dt +ᵥ t).val = dt + t.val := rfl
