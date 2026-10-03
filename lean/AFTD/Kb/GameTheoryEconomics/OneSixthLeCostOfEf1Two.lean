import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CostOfEf1
import AFTD.Kb.GameTheoryEconomics.Ef1CostGapInstance
import AFTD.Kb.GameTheoryEconomics.Ef1CostGapInstanceSpec
import AFTD.Kb.GameTheoryEconomics.Ef1GapSetTwoAgentsLe
import AFTD.Kb.GameTheoryEconomics.IsNormalizedChoresInstance
import AFTD.Kb.GameTheoryEconomics.OptEf1SocialCost
import AFTD.Kb.GameTheoryEconomics.OptSocialCost

/-!
# one_sixth_le_cost_of_ef1_two

Topic: fair_division   Node: 515886ba60c9

The cost of EF1 for two agents is at least 1/6.
-/

/-- **The cost of EF1 for two agents is at least `1/6`.** -/
theorem one_sixth_le_cost_of_ef1_two : 1 / 6 ≤ cost_of_ef1 2 := by
  refine _root_.le_of_forall_pos_le_add (fun ε hε => ?_)
  set δ := min ε (1 / 6) with hδ
  have hδ0 : 0 < δ := lt_min hε (by norm_num)
  have hδ1 : δ ≤ 1 / 6 := min_le_right _ _
  have hδε : δ ≤ ε := min_le_left _ _
  have hmem : 1 / 6 - δ ∈ {d : ℝ | ∃ (m : ℕ) (c : Fin 2 → Fin m → ℝ),
      is_normalized_chores_instance c ∧ d = opt_ef1_social_cost c - opt_social_cost c} :=
    ⟨3, ef1_cost_gap_instance δ, (ef1_cost_gap_instance_spec δ hδ0 hδ1).1,
      (ef1_cost_gap_instance_spec δ hδ0 hδ1).2.2.2.symm⟩
  have := le_csSup ⟨3 - 2 * Real.sqrt 2, ef1_gap_set_two_agents_le⟩ hmem
  unfold cost_of_ef1
  linarith
