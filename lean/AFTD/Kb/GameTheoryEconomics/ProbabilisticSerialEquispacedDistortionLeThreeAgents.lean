import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialLineDistortionLeThreeAgents
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialLineCost
import AFTD.Kb.GameTheoryEconomics.LineMinMatchingCost
import AFTD.Kb.GameTheoryEconomics.IsLineDistancePreferenceProfile

/-!
# probabilistic_serial_equispaced_distortion_le_three_agents

Topic: social_choice   Node: 850bf3de259c

Provenance: original. Related work: OP-1441

For three agents at real locations and three equispaced items at 0, 1, and 2, the probabilistic serial cost under any distance preference profile is at most [1 + H_1 + H_1] = 3 times the minimum matching cost OPT.
-/

/-- Case n = 3 of OP-1441: the harmonic distortion upper bound holds for three agents and equispaced items. -/
theorem probabilistic_serial_equispaced_distortion_le_three_agents (a : Fin 3 → ℝ)
    (pref : Fin 3 → Equiv.Perm (Fin 3))
    (h : is_line_distance_preference_profile a (fun (j : Fin 3) => (j : ℝ)) pref) :
    probabilistic_serial_line_cost a (fun (j : Fin 3) => (j : ℝ)) pref ≤
      (1 + (harmonic (3 / 2) : ℝ) + (harmonic ((3 - 1) / 2) : ℝ)) *
        line_min_matching_cost a (fun (j : Fin 3) => (j : ℝ)) := by
  have h3 : (1 + (harmonic (3 / 2) : ℝ) + (harmonic ((3 - 1) / 2) : ℝ)) = 3 := by norm_num
  rw [h3]
  exact probabilistic_serial_line_distortion_le_three_agents a (fun j => (j : ℝ)) pref h
