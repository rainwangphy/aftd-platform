import AFTD.Prelude
import AFTD.Kb.Physics.TimeMan
import AFTD.Kb.Physics.TimeManInstTopologicalSpace

/-!
# TimeMan.val_surjective

Topic: classical_mechanics   Node: a0d263465f9e

Provenance: formalization of a published result. Source: Physlib, `TimeMan.val_surjective`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Time/TimeMan.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

TimeMan.val_surjective
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
lemma TimeMan.val_surjective : Function.Surjective TimeMan.val := by
  intro t
  use { val := t }
