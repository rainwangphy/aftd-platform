import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Ef1GapLeTwoAgents
import AFTD.Kb.GameTheoryEconomics.IsNormalizedChoresInstance
import AFTD.Kb.GameTheoryEconomics.OptEf1SocialCost
import AFTD.Kb.GameTheoryEconomics.OptSocialCost

/-!
# ef1_gap_set_two_agents_le

Topic: fair_division   Node: 3062ffb7768a

Provenance: helper lemma. step towards cost_of_ef1_two_le / one_sixth_le_cost_of_ef1_two (cost of EF1 for two agents lies in [1/6, 3 - 2 sqrt 2]; A Fair Allocation is Approximately Optimal for Indivisible Chores, or Is It?, arXiv:2410.15738 v1, Thm 7 states the lower bound 1 - 1/n, whose construction needs n >= 3)

The set of gaps whose supremum is `cost_of_ef1 2` is bounded by `3 - 2√2`.
-/

/-- The set of gaps whose supremum is `cost_of_ef1 2` is bounded by `3 - 2√2`. -/
theorem ef1_gap_set_two_agents_le :
    ∀ d ∈ {d : ℝ | ∃ (m : ℕ) (c : Fin 2 → Fin m → ℝ), is_normalized_chores_instance c ∧
      d = opt_ef1_social_cost c - opt_social_cost c}, d ≤ 3 - 2 * Real.sqrt 2 := by
  rintro d ⟨m, c, hc, rfl⟩
  exact ef1_gap_le_two_agents c hc
