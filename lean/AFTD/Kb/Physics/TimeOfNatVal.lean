import AFTD.Prelude
import AFTD.Kb.Physics.Time
import AFTD.Kb.Physics.TimeInstOfNat
import AFTD.Kb.Physics.TimeVaddVal
import AFTD.Kb.Physics.TimeVsubEqVal
import AFTD.Kb.Physics.TimeNatCastVal
import AFTD.Kb.Physics.TimeNatCastZero
import AFTD.Kb.Physics.TimeNatCastOne
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
# Time.ofNat_val

Topic: classical_mechanics   Node: 1e8898fe8fb2

Provenance: formalization of a published result. Source: Physlib, `Time.ofNat_val`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Time/InnerProductSpace.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Time.ofNat_val
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
@[simp]
lemma Time.ofNat_val {n : ℕ} : val (OfNat.ofNat n : Time) = n := rfl
