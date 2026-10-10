import AFTD.Prelude
import AFTD.Kb.Physics.BlackBody
import AFTD.Kb.Physics.SpeedOfLight
import AFTD.Kb.Physics.ConstantsH
import AFTD.Kb.Physics.ConstantsKB
import AFTD.Kb.Physics.TemperatureToReal
import AFTD.Kb.Physics.SpeedOfLightValOne
import AFTD.Kb.Physics.SpeedOfLightValPos
import AFTD.Kb.Physics.SpeedOfLightValNonneg
import AFTD.Kb.Physics.SpeedOfLightValNeZero
import AFTD.Kb.Physics.TemperatureBetaOfBeta
import AFTD.Kb.Physics.TemperatureOfBetaBeta
import AFTD.Kb.Physics.TemperatureOfNNReal
import AFTD.Kb.Physics.TemperatureOfNNRealVal
import AFTD.Kb.Physics.TemperatureCoeOfNNRealCoe
import AFTD.Kb.Physics.TemperatureCoeOfNNRealReal
import AFTD.Kb.Physics.TemperatureOfRealNonneg
import AFTD.Kb.Physics.TemperatureOfRealNonnegVal
import AFTD.Kb.Physics.ConstantsPiPos
import AFTD.Kb.Physics.ConstantsPiNonneg
import AFTD.Kb.Physics.ConstantsPiNeZero
import AFTD.Kb.Physics.ConstantsHPos
import AFTD.Kb.Physics.ConstantsHNonneg
import AFTD.Kb.Physics.ConstantsHNeZero
import AFTD.Kb.Physics.SpeedOfLightInstCoeReal
import AFTD.Kb.Physics.SpeedOfLightInstOne
import AFTD.Kb.Physics.TemperatureInstCoeNNReal
import AFTD.Kb.Physics.TemperatureInstCoeReal
import AFTD.Kb.Physics.TemperatureInstTopologicalSpace
import AFTD.Kb.Physics.TemperatureInstZero

/-!
# BlackBody.spectralRadiance

Topic: quantum_mechanics   Node: 231276b752d4

Provenance: formalization of a published result. Source: Physlib, `BlackBody.spectralRadiance`. Lean proof by Samyak Rai, Dwanith C. Jayanth, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Blackbody/PlancksLaw.lean (Copyright (c) 2026 Samyak Rai. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The spectral radiance per unit frequency of blackbody radiation at frequency `ν` for a black body `B` and speed of light `c`: `B(ν, T) = 2 h ν³ / c² · 1 / (e^{h ν / (k_B T)} - 1)` By the homogeneity and isotropy of blackbody radiation, the spectral radiance is independent of position and direction, so it depends only on frequency and temperature. Extended by zero outside the physical domain `0 < ν`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Constants in
/-- The spectral radiance per unit frequency of blackbody radiation at frequency `ν` for a black body `B` and speed of light `c`: `B(ν, T) = 2 h ν³ / c² · 1 / (e^{h ν / (k_B T)} - 1)` By the homogeneity and isotropy of blackbody radiation, the spectral radiance is independent of position and direction, so it depends only on frequency and temperature. Extended by zero outside the physical domain `0 < ν`. -/
noncomputable def BlackBody.spectralRadiance (B : BlackBody) (c : SpeedOfLight) (ν : ℝ) : ℝ :=
  if 0 < ν then
    2 * h * ν ^ 3 / ((c : ℝ) ^ 2 * (Real.exp (h * ν / (kB * (B.T : ℝ))) - 1))
  else 0
