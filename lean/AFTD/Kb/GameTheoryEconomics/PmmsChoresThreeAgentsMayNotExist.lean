import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsPmmsFairChores
import AFTD.Kb.GameTheoryEconomics.Pmms3cCost
import AFTD.Kb.GameTheoryEconomics.Pmms3cCheck
import AFTD.Kb.GameTheoryEconomics.Pmms3cVerifySound

/-!
# pmms_chores_three_agents_may_not_exist

Topic: fair_division   Node: 8ff86cec309a

PMMS allocations of chores need not exist already for three agents: there are strictly positive additive costs of three agents for nine chores such that no allocation is pairwise-MMS for every agent. arXiv:2609.10493 obtains non-existence for chores only through EFX non-existence, which needs at least four agents; with two agents a PMMS allocation always exists, so three is the least number of agents.
-/

theorem pmms_chores_three_agents_may_not_exist : ∃ c : Fin 3 → Fin 9 → ℝ, (∀ i g, 0 < c i g) ∧ ∀ σ : Fin 9 → Fin 3, ∃ i, ¬ is_pmms_fair_chores c σ i := by
  refine ⟨fun i g => (pmms3c_cost i g : ℝ), fun i g => ?_, fun σ => ?_⟩
  · have : 0 < pmms3c_cost i g := by revert i g; decide
    show (0 : ℝ) < (pmms3c_cost i g : ℝ)
    exact_mod_cast this
  have hσ : σ = ![σ 0, σ 1, σ 2, σ 3, σ 4, σ 5, σ 6, σ 7, σ 8] := by
    funext x; fin_cases x <;> rfl
  have hc := pmms3c_check (σ 0) (σ 1) (σ 2) (σ 3) (σ 4) (σ 5) (σ 6) (σ 7) (σ 8)
  rw [← hσ] at hc
  exact ⟨_, pmms3c_verify_sound σ _ hc⟩
