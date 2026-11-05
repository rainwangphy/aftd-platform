import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialLineThreeAgentsLeOfFirstChoices01
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialLineThreeAgentsLeOfFirstChoices02
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialLineThreeAgentsLeOfFirstChoices10
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialLineThreeAgentsLeOfFirstChoices12
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialLineThreeAgentsLeOfFirstChoices20
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialLineThreeAgentsLeOfFirstChoices21
import AFTD.Kb.GameTheoryEconomics.LineMinMatchingCost
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialLineCost
import AFTD.Kb.GameTheoryEconomics.IsLineDistancePreferenceProfile

/-!
# probabilistic_serial_line_distortion_le_three_agents

Topic: social_choice   Node: dc9aa6e348d2

Provenance: original. Related work: Related work: OP-1158, case n = 3; arXiv:2611.05777 bounds probabilistic serial on general metrics (exponential distortion), not this line case

Case n = 3 of OP-1158: for three agents at real positions a_0, a_1, a_2 and three items at real positions b_0, b_1, b_2, with each agent ranking the items by distance (ties broken arbitrarily), the cost of the probabilistic serial assignment, sum_ij X_ij |a_i - b_j|, is at most 3 times the minimum perfect-matching cost.
-/

theorem probabilistic_serial_line_distortion_le_three_agents (a b : Fin 3 → ℝ)
    (pref : Fin 3 → Equiv.Perm (Fin 3)) (h : is_line_distance_preference_profile a b pref) :
    probabilistic_serial_line_cost a b pref ≤ 3 * line_min_matching_cost a b := by
  obtain ⟨σ0, -, hσ0⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := Equiv.Perm (Fin 3)))
    (fun σ : Equiv.Perm (Fin 3) => ∑ i, |a i - b (σ i)|)
  have hopt : line_min_matching_cost a b = ∑ i, |a i - b (σ0 i)| := hσ0
  rw [hopt]
  have hne : pref 0 0 ≠ pref 0 1 := (pref 0).injective.ne (by decide)
  have key : ∀ x y : Fin 3, x ≠ y → (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = 2) ∨ (x = 1 ∧ y = 0) ∨
      (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 0) ∨ (x = 2 ∧ y = 1) := by decide
  rcases key _ _ hne with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact probabilistic_serial_line_three_agents_le_of_first_choices_01 a b pref h hx hy σ0
  · exact probabilistic_serial_line_three_agents_le_of_first_choices_02 a b pref h hx hy σ0
  · exact probabilistic_serial_line_three_agents_le_of_first_choices_10 a b pref h hx hy σ0
  · exact probabilistic_serial_line_three_agents_le_of_first_choices_12 a b pref h hx hy σ0
  · exact probabilistic_serial_line_three_agents_le_of_first_choices_20 a b pref h hx hy σ0
  · exact probabilistic_serial_line_three_agents_le_of_first_choices_21 a b pref h hx hy σ0
