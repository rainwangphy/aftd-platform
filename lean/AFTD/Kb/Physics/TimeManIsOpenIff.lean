import AFTD.Prelude
import AFTD.Kb.Physics.TimeMan
import AFTD.Kb.Physics.TimeManInstTopologicalSpace
import AFTD.Kb.Physics.TimeManValIsOpenEmbedding
import AFTD.Kb.Physics.TimeManValRange

/-!
# TimeMan.isOpen_iff

Topic: classical_mechanics   Node: 605c08f44421

Provenance: formalization of a published result. Source: Physlib, `TimeMan.isOpen_iff`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Time/TimeMan.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

TimeMan.isOpen_iff
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
lemma TimeMan.isOpen_iff {s : Set TimeMan} :
    IsOpen s ↔ IsOpen (TimeMan.val '' s) :=
  Topology.IsOpenEmbedding.isOpen_iff_image_isOpen val_isOpenEmbedding
