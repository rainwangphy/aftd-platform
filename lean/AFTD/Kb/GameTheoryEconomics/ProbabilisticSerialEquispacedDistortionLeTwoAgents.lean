import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialLineDistortionLeTwoAgents
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialLineCost
import AFTD.Kb.GameTheoryEconomics.LineMinMatchingCost
import AFTD.Kb.GameTheoryEconomics.IsLineDistancePreferenceProfile

/-!
# probabilistic_serial_equispaced_distortion_le_two_agents

Topic: social_choice   Node: 48433b5414e5

Provenance: original. Related work: OP-1441

For two agents at real locations and two equispaced items at 0 and 1, the probabilistic serial cost under any distance preference profile is at most [1 + H_1 + H_0] = 2 times the minimum matching cost OPT.
-/

/-- Case n = 2 of OP-1441: the harmonic distortion upper bound holds for two agents and equispaced items. -/
theorem probabilistic_serial_equispaced_distortion_le_two_agents (a : Fin 2 → ℝ)
    (pref : Fin 2 → Equiv.Perm (Fin 2))
    (h : is_line_distance_preference_profile a (fun (j : Fin 2) => (j : ℝ)) pref) :
    probabilistic_serial_line_cost a (fun (j : Fin 2) => (j : ℝ)) pref ≤
      (1 + (harmonic (2 / 2) : ℝ) + (harmonic ((2 - 1) / 2) : ℝ)) *
        line_min_matching_cost a (fun (j : Fin 2) => (j : ℝ)) := by
  have h_bound := probabilistic_serial_line_distortion_le_two_agents a (fun (j : Fin 2) => (j : ℝ)) pref h
  have h_harm_0 : harmonic 0 = 0 := harmonic_zero
  have h_harm_1 : harmonic 1 = 1 := by
    change harmonic (0 + 1) = 1
    rw [harmonic_succ, harmonic_zero]
    simp
  have h_coef : (1 + (harmonic (2 / 2) : ℝ) + (harmonic ((2 - 1) / 2) : ℝ)) = 2 := by
    have h1 : 2 / 2 = 1 := rfl
    have h0 : (2 - 1) / 2 = 0 := rfl
    rw [h1, h0, h_harm_0, h_harm_1]
    push_cast
    ring
  rw [h_coef]
  exact h_bound
