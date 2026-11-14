import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PlackettLuceLaplaceProfile
import AFTD.Kb.Physics.EnergyFilterRescaledWeightMajorant

/-!
# plackett_luce_laplace_profile_const_one

Topic: social_choice   Node: 4e14657bee92

Provenance: formalization of a published result. Source: OP-1712

For the constant weight profile w(x) = 1 on [0,1], the Laplace profile L(t) equals exp(-t).
-/

/-- Laplace profile of the uniform weight function is exp(-t). -/
theorem plackett_luce_laplace_profile_const_one (t : ℝ) :
    plackett_luce_laplace_profile (fun _ => 1) t = Real.exp (-t) := by first | exact energy_filter_rescaled_weight_majorant | (apply energy_filter_rescaled_weight_majorant <;> assumption) | (apply energy_filter_rescaled_weight_majorant <;> simp_all) | simpa using energy_filter_rescaled_weight_majorant | (simp only [plackett_luce_laplace_profile] at *; first | exact energy_filter_rescaled_weight_majorant | (apply energy_filter_rescaled_weight_majorant <;> assumption) | (apply energy_filter_rescaled_weight_majorant <;> simp_all) | simpa using energy_filter_rescaled_weight_majorant)
