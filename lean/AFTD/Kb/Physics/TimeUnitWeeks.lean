import AFTD.Prelude
import AFTD.Kb.Physics.TimeUnit
import AFTD.Kb.Physics.PositiveRealUnitCoreScale
import AFTD.Kb.Physics.InstPositiveRealUnitCoreTimeUnit
import AFTD.Kb.Physics.TimeUnitDays
import AFTD.Kb.Physics.TimeUnitMinutes
import AFTD.Kb.Physics.TimeUnitSeconds
import AFTD.Kb.Physics.PositiveRealUnitCore
import AFTD.Kb.Physics.PositiveRealUnitCoreValNeZero
import AFTD.Kb.Physics.PositiveRealUnitCoreDivPos
import AFTD.Kb.Physics.PositiveRealUnitCoreDivNeZero
import AFTD.Kb.Physics.PositiveRealUnitCoreDivSelf
import AFTD.Kb.Physics.PositiveRealUnitCoreDivMulDivCoe
import AFTD.Kb.Physics.PositiveRealUnitCoreScaleVal
import AFTD.Kb.Physics.PositiveRealUnitCoreScaleDivSelf
import AFTD.Kb.Physics.PositiveRealUnitCoreSelfDivScale
import AFTD.Kb.Physics.PositiveRealUnitCoreScaleOne
import AFTD.Kb.Physics.PositiveRealUnitCoreScaleDivScale
import AFTD.Kb.Physics.PositiveRealUnitCoreScaleScale
import AFTD.Kb.Physics.PositiveRealUnitCoreScaleDiv
import AFTD.Kb.GameTheoryEconomics.Mnw2LbVal
import AFTD.Kb.GameTheoryEconomics.SpxX

/-!
# TimeUnit.weeks

Topic: classical_mechanics   Node: a35bfc966eee

Provenance: formalization of a published result. Source: Physlib, `TimeUnit.weeks`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Time/TimeUnit.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The time unit of 7 day weeks.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
open NNReal in
open PositiveRealUnitCore in
/-- The time unit of 7 day weeks. -/
noncomputable def TimeUnit.weeks : TimeUnit := scale (7 * 24 * 60 * 60) seconds
