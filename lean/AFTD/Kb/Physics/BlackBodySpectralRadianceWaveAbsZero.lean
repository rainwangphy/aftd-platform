import AFTD.Prelude
import AFTD.Kb.Physics.SpeedOfLight
import AFTD.Kb.Physics.BlackBodySpectralRadianceWave
import AFTD.Kb.Physics.BlackBody
import AFTD.Kb.Physics.Temperature
import AFTD.Kb.Physics.TemperatureInstZero
import AFTD.Kb.Physics.BlackBodySpectralRadiance
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

/-!
# BlackBody.spectralRadianceWave_absZero

Topic: quantum_mechanics   Node: 9feef0ea48ec

Provenance: formalization of a published result. Source: Physlib, `BlackBody.spectralRadianceWave_absZero`. Lean proof by Samyak Rai, Dwanith C. Jayanth, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Blackbody/PlancksLaw.lean (Copyright (c) 2026 Samyak Rai. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The spectral radiance per unit wavelength vanishes at absolute zero.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Constants in
/-- The spectral radiance per unit wavelength vanishes at absolute zero. -/
lemma BlackBody.spectralRadianceWave_absZero (c : SpeedOfLight) (lam : ℝ) :
    spectralRadianceWave ⟨0⟩ c lam = 0 := by
  unfold spectralRadianceWave
  split_ifs with hlam
  · simp [show ((⟨0⟩ : BlackBody).T : ℝ) = 0 from rfl]
  · rfl
