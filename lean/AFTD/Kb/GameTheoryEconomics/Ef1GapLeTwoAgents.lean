import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Ef1costSocialCostEq
import AFTD.Kb.GameTheoryEconomics.ExistsEf1SocialCostLeOptAddTwoAgents
import AFTD.Kb.GameTheoryEconomics.IsNormalizedChoresInstance
import AFTD.Kb.GameTheoryEconomics.OptEf1SocialCost
import AFTD.Kb.GameTheoryEconomics.OptSocialCost
import AFTD.Kb.GameTheoryEconomics.SocialCost

/-!
# ef1_gap_le_two_agents

Topic: fair_division   Node: 50ff13812692

For two agents with normalized additive chores, the best EF1 social cost exceeds the optimal social cost by at most 3 - 2 sqrt 2.
-/

/-- For two agents, the gap `min_{EF1} SC - OPT` of every normalised instance is at most `3 - 2√2`. -/
theorem ef1_gap_le_two_agents {m : ℕ} (c : Fin 2 → Fin m → ℝ)
    (hc : is_normalized_chores_instance c) :
    opt_ef1_social_cost c - opt_social_cost c ≤ 3 - 2 * Real.sqrt 2 := by
  obtain ⟨σ, hσ, hle⟩ := exists_ef1_social_cost_le_opt_add_two_agents c hc
  have hnn : ∀ τ, 0 ≤ social_cost c τ := by
    intro τ
    rw [ef1cost_social_cost_eq]
    exact Finset.sum_nonneg (fun j _ => hc.1 _ _)
  have h1 : opt_ef1_social_cost c ≤ social_cost c σ := by
    refine csInf_le ⟨0, ?_⟩ ⟨σ, hσ, rfl⟩
    rintro _ ⟨τ, -, rfl⟩
    exact hnn τ
  have h2 : social_cost c σ - (3 - 2 * Real.sqrt 2) ≤ opt_social_cost c :=
    le_ciInf (fun τ => by linarith [hle τ])
  linarith
