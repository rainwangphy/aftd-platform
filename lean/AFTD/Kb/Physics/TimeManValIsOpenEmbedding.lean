import AFTD.Prelude
import AFTD.Kb.Physics.TimeMan
import AFTD.Kb.Physics.TimeManInstTopologicalSpace
import AFTD.Kb.Physics.TimeManValInjective
import AFTD.Kb.Physics.TimeManValRange

/-!
# TimeMan.val_isOpenEmbedding

Topic: classical_mechanics   Node: e1aea3015aa6

Provenance: formalization of a published result. Source: Physlib, `TimeMan.val_isOpenEmbedding`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Time/TimeMan.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

TimeMan.val_isOpenEmbedding
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
lemma TimeMan.val_isOpenEmbedding : Topology.IsOpenEmbedding TimeMan.val where
  eq_induced := rfl
  isOpen_range := by
    simp
  injective := val_injective
