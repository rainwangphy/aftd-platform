import AFTD.Prelude
import AFTD.Kb.Physics.TimeMan
import AFTD.Kb.Physics.TimeManValRange
import AFTD.Kb.Physics.TimeManInstTopologicalSpace

/-!
# TimeMan.val_injective

Topic: classical_mechanics   Node: f9baa8f2f791

Provenance: formalization of a published result. Source: Physlib, `TimeMan.val_injective`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Time/TimeMan.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

TimeMan.val_injective
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
lemma TimeMan.val_injective : Function.Injective TimeMan.val := by
  intro t1 t2 h
  cases t1
  cases t2
  simp_all
