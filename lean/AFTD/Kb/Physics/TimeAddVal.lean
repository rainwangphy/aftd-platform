import AFTD.Prelude
import AFTD.Kb.Physics.Time
import AFTD.Kb.Physics.TimeInstAdd
import AFTD.Kb.Physics.TimeVaddVal
import AFTD.Kb.Physics.TimeVsubEqVal
import AFTD.Kb.Physics.TimeNatCastVal
import AFTD.Kb.Physics.TimeNatCastZero
import AFTD.Kb.Physics.TimeNatCastOne
import AFTD.Kb.Physics.TimeOfNatVal
import AFTD.Kb.Physics.TimeZeroVal
import AFTD.Kb.Physics.TimeEqZeroIff
import AFTD.Kb.Physics.TimeOneVal
import AFTD.Kb.Physics.TimeEqOneIff
import AFTD.Kb.Physics.TimeRealCastOfNatCast
import AFTD.Kb.Physics.TimeDefaultEqZero
import AFTD.Kb.Physics.TimeInstNonempty
import AFTD.Kb.Physics.TimeInstVAddReal
import AFTD.Kb.Physics.TimeInstVSubReal
import AFTD.Kb.Physics.TimeInstAddTorsorReal
import AFTD.Kb.Physics.TimeInstMetricSpace
import AFTD.Kb.Physics.TimeInstNormedAddTorsorReal
import AFTD.Kb.Physics.TimeInstChartedSpaceReal
import AFTD.Kb.Physics.TimeInstIsManifoldRealModelWithCornersSelfTopWithTopENat
import AFTD.Kb.Physics.TimeInstNatCast
import AFTD.Kb.Physics.TimeInstOfNat
import AFTD.Kb.Physics.TimeInstCoeReal
import AFTD.Kb.Physics.TimeInstCoeReal1
import AFTD.Kb.Physics.TimeInstInhabited
import AFTD.Kb.Physics.TimeInstLE
import AFTD.Kb.Physics.TimeInstPartialOrder

/-!
# Time.add_val

Topic: classical_mechanics   Node: 3704d5bb70a8

Provenance: formalization of a published result. Source: Physlib, `Time.add_val`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Time/InnerProductSpace.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Time.add_val
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
@[simp]
lemma Time.add_val (t1 t2 : Time) :
    (t1 + t2).val = t1.val + t2.val := rfl
