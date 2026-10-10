import AFTD.Prelude
import AFTD.Kb.Physics.TimeMan
import AFTD.Kb.Physics.TimeManValSurjective
import AFTD.Kb.Physics.TimeManInstTopologicalSpace

/-!
# TimeMan.val_range

Topic: classical_mechanics   Node: 3c750f532314

Provenance: formalization of a published result. Source: Physlib, `TimeMan.val_range`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Time/TimeMan.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

TimeMan.val_range
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
@[simp]
lemma TimeMan.val_range : Set.range val = Set.univ := by
  refine Set.range_eq_univ.mpr val_surjective
