import AFTD.Prelude
import AFTD.Kb.Physics.TimeUnit
import AFTD.Kb.Physics.PositiveRealUnitCoreScale
import AFTD.Kb.Physics.InstPositiveRealUnitCoreTimeUnit
import AFTD.Kb.Physics.TimeUnitFemtoseconds
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
import AFTD.Kb.GameTheoryEconomics.PcyMu

/-!
# TimeUnit.picoseconds

Topic: classical_mechanics   Node: 459c2be90eec

Provenance: formalization of a published result. Source: Physlib, `TimeUnit.picoseconds`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Time/TimeUnit.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The time unit of picoseconds (10⁻¹² of a second).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
open NNReal in
open PositiveRealUnitCore in
/-- The time unit of picoseconds (10⁻¹² of a second). -/
noncomputable def TimeUnit.picoseconds : TimeUnit := scale ((1/10) ^ (12)) seconds
