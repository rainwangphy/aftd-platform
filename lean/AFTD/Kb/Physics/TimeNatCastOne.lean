import AFTD.Prelude
import AFTD.Kb.Physics.Time
import AFTD.Kb.Physics.TimeInstNatCast
import AFTD.Kb.Physics.TimeInstOfNat
import AFTD.Kb.Physics.TimeVaddVal
import AFTD.Kb.Physics.TimeVsubEqVal
import AFTD.Kb.Physics.TimeNatCastVal
import AFTD.Kb.Physics.TimeNatCastZero
import AFTD.Kb.Physics.TimeInstNonempty
import AFTD.Kb.Physics.TimeInstVAddReal
import AFTD.Kb.Physics.TimeInstVSubReal
import AFTD.Kb.Physics.TimeInstAddTorsorReal
import AFTD.Kb.Physics.TimeInstMetricSpace
import AFTD.Kb.Physics.TimeInstNormedAddTorsorReal
import AFTD.Kb.Physics.TimeInstChartedSpaceReal
import AFTD.Kb.Physics.TimeInstIsManifoldRealModelWithCornersSelfTopWithTopENat

/-!
# Time.natCast_one

Topic: classical_mechanics   Node: fb3a7d1d9cfb

Provenance: formalization of a published result. Source: Physlib, `Time.natCast_one`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Time/InnerProductSpace.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Time.natCast_one
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
@[simp]
lemma Time.natCast_one : ((1 : ℕ) : Time) = 1 := rfl
