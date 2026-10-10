import AFTD.Prelude
import AFTD.Kb.Physics.LengthUnit
import AFTD.Kb.Physics.PositiveRealUnitCoreInstHDiv
import AFTD.Kb.Physics.InstPositiveRealUnitCoreLengthUnit
import AFTD.Kb.Physics.LengthUnitFurlongs
import AFTD.Kb.Physics.LengthUnitYards
import AFTD.Kb.Physics.PositiveRealUnitCoreScale
import AFTD.Kb.Physics.LengthUnitMeters
import AFTD.Kb.Physics.PositiveRealUnitCoreScaleDivScale
import AFTD.Kb.Physics.PositiveRealUnitCoreDivSelf
import AFTD.Kb.Physics.PositiveRealUnitCore
import AFTD.Kb.Physics.PositiveRealUnitCoreValNeZero
import AFTD.Kb.Physics.PositiveRealUnitCoreDivPos
import AFTD.Kb.Physics.PositiveRealUnitCoreDivNeZero
import AFTD.Kb.Physics.PositiveRealUnitCoreDivMulDivCoe
import AFTD.Kb.Physics.PositiveRealUnitCoreScaleVal
import AFTD.Kb.Physics.PositiveRealUnitCoreScaleDivSelf
import AFTD.Kb.Physics.PositiveRealUnitCoreSelfDivScale
import AFTD.Kb.Physics.PositiveRealUnitCoreScaleOne
import AFTD.Kb.Physics.PositiveRealUnitCoreScaleScale
import AFTD.Kb.Physics.PositiveRealUnitCoreScaleDiv

/-!
# LengthUnit.furlongs_div_yards

Topic: classical_mechanics   Node: de200cf508f2

Provenance: formalization of a published result. Source: Physlib, `LengthUnit.furlongs_div_yards`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/LengthUnit.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

There are exactly 220 yards in a furlong.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
open PositiveRealUnitCore in
/-- There are exactly 220 yards in a furlong. -/
lemma LengthUnit.furlongs_div_yards : furlongs / yards = (⟨220, by norm_num⟩ : ℝ≥0) := NNReal.eq <| by
  simp [furlongs, yards]
  show (201.168 : ℝ) / 0.9144 = ((⟨220, by norm_num⟩ : ℝ≥0) : ℝ)
  push_cast
  norm_num
