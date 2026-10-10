import AFTD.Prelude
import AFTD.Kb.Physics.LengthUnit
import AFTD.Kb.Physics.PositiveRealUnitCoreScale
import AFTD.Kb.Physics.InstPositiveRealUnitCoreLengthUnit
import AFTD.Kb.Physics.LengthUnitFemtometers
import AFTD.Kb.Physics.LengthUnitMeters
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
# LengthUnit.centimeters

Topic: classical_mechanics   Node: 34602b3f084f

Provenance: formalization of a published result. Source: Physlib, `LengthUnit.centimeters`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/LengthUnit.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The length unit of centimeters (10⁻² of a meter).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
open PositiveRealUnitCore in
/-- The length unit of centimeters (10⁻² of a meter). -/
noncomputable def LengthUnit.centimeters : LengthUnit := scale ((1/10) ^ (2)) meters
