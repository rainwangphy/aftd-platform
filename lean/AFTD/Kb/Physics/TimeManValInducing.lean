import AFTD.Prelude
import AFTD.Kb.Physics.TimeMan
import AFTD.Kb.Physics.TimeManInstTopologicalSpace
import AFTD.Kb.Physics.TimeManValRange

/-!
# TimeMan.val_inducing

Topic: classical_mechanics   Node: 1d6ef86e713b

Provenance: formalization of a published result. Source: Physlib, `TimeMan.val_inducing`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Time/TimeMan.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

TimeMan.val_inducing
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
lemma TimeMan.val_inducing : Topology.IsInducing TimeMan.val where
  eq_induced := rfl
