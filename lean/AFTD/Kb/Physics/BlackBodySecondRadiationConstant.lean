import AFTD.Prelude
import AFTD.Kb.Physics.SpeedOfLight
import AFTD.Kb.Physics.ConstantsH
import AFTD.Kb.Physics.ConstantsKB
import AFTD.Kb.Physics.SpeedOfLightValOne
import AFTD.Kb.Physics.SpeedOfLightValPos
import AFTD.Kb.Physics.SpeedOfLightValNonneg
import AFTD.Kb.Physics.SpeedOfLightValNeZero
import AFTD.Kb.Physics.ConstantsPiPos
import AFTD.Kb.Physics.ConstantsPiNonneg
import AFTD.Kb.Physics.ConstantsPiNeZero
import AFTD.Kb.Physics.ConstantsHPos
import AFTD.Kb.Physics.ConstantsHNonneg
import AFTD.Kb.Physics.ConstantsHNeZero
import AFTD.Kb.Physics.SpeedOfLightInstCoeReal
import AFTD.Kb.Physics.SpeedOfLightInstOne

/-!
# BlackBody.secondRadiationConstant

Topic: quantum_mechanics   Node: 5f7747927f5d

Provenance: formalization of a published result. Source: Physlib, `BlackBody.secondRadiationConstant`. Lean proof by Samyak Rai, Dwanith C. Jayanth, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Blackbody/PlancksLaw.lean (Copyright (c) 2026 Samyak Rai. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The second radiation constant `c₂ = h c / kB`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Constants in
/-- The second radiation constant `c₂ = h c / kB`. -/
noncomputable def BlackBody.secondRadiationConstant (c : SpeedOfLight) : ℝ :=
  (h : ℝ) * (c : ℝ) / kB
