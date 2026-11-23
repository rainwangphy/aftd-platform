import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SampfordConsecutiveHouseCouplingLossDelta
import AFTD.Kb.GameTheoryEconomics.SampfordConsecutiveHouseCouplingLossDeltaSixGeAsymmetric

/-!
# sampford_balanced_family_not_attain_delta_six

Topic: social_choice   Node: 8d4e6af850bc

Provenance: original. Related work: Correa et al., arXiv:2405.03687

The balanced two-group family does not attain Delta_6, as the maximal consecutive-house coupling loss Delta_6 strictly exceeds the balanced family limit 31/159.
-/

/-- The balanced two-group family does not attain Delta_6 for Sampford consecutive-house coupling loss. -/
theorem sampford_balanced_family_not_attain_delta_six :
    (31 : ℝ) / 159 < sampfordConsecutiveHouseCouplingLossDelta 6 := by
  exact lt_of_lt_of_le (by norm_num) sampford_consecutive_house_coupling_loss_delta_six_ge_asymmetric
