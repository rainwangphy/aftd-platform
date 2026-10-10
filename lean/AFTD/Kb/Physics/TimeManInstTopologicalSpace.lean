import AFTD.Prelude
import AFTD.Kb.Physics.TimeMan

/-!
# TimeMan.instTopologicalSpace

Topic: classical_mechanics   Node: d44a9fcfa5d0

Provenance: formalization of a published result. Source: Physlib, `TimeMan.instTopologicalSpace`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Time/TimeMan.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The instance of a topological space on `TimeMan` induced by the map `TimeMan.val`. s
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The instance of a topological space on `TimeMan` induced by the map `TimeMan.val`. s -/
instance TimeMan.instTopologicalSpace : TopologicalSpace TimeMan := TopologicalSpace.induced TimeMan.val
  PseudoMetricSpace.toUniformSpace.toTopologicalSpace
