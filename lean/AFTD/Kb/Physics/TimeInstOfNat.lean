import AFTD.Prelude
import AFTD.Kb.Physics.Time
import AFTD.Kb.Physics.TimeVaddVal
import AFTD.Kb.Physics.TimeVsubEqVal
import AFTD.Kb.Physics.TimeInstNonempty
import AFTD.Kb.Physics.TimeInstVAddReal
import AFTD.Kb.Physics.TimeInstVSubReal
import AFTD.Kb.Physics.TimeInstAddTorsorReal
import AFTD.Kb.Physics.TimeInstMetricSpace
import AFTD.Kb.Physics.TimeInstNormedAddTorsorReal
import AFTD.Kb.Physics.TimeInstChartedSpaceReal
import AFTD.Kb.Physics.TimeInstIsManifoldRealModelWithCornersSelfTopWithTopENat
import AFTD.Kb.Physics.TimeInstNatCast

/-!
# Time.instOfNat

Topic: classical_mechanics   Node: 06bb681739b5

Provenance: formalization of a published result. Source: Physlib, `Time.instOfNat`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Time/InnerProductSpace.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The casting of a natural number to an element of `Time`. This corresponds to a choice of (1) zero point in time, and (2) a choice of metric on time (defining `1`).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The casting of a natural number to an element of `Time`. This corresponds to a choice of (1) zero point in time, and (2) a choice of metric on time (defining `1`). -/
instance Time.instOfNat {n : ℕ} : OfNat Time n where
  ofNat := ⟨n⟩
