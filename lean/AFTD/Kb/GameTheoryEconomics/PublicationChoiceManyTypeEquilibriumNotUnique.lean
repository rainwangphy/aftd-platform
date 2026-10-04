import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PcpIsEquilibrium
import AFTD.Kb.GameTheoryEconomics.PcpIsValid
import AFTD.Kb.GameTheoryEconomics.PcpMonotoneCostRatio
import AFTD.Kb.GameTheoryEconomics.PcpNoncompetitiveVenue
import AFTD.Kb.GameTheoryEconomics.PublicationChoiceThreeTypesThreeEquilibria

/-!
# publication_choice_many_type_equilibrium_not_unique

Topic: equilibria   Node: 4f47f799bc14

Conjecture 4.2 of arXiv:2511.13678 is false: not every Publication Choice Problem with three strictly ordered types satisfying the standing assumptions, Assumption 1 and Assumption 2 has a unique pure-strategy equilibrium.
-/

/-- Conjecture 4.2 of arXiv:2511.13678 is false: not every Publication Choice Problem with three strictly ordered types satisfying the standing assumptions, Assumption 1 (MCR) and Assumption 2 (non-competitive venue) has a unique pure-strategy equilibrium. -/
theorem publication_choice_many_type_equilibrium_not_unique :
    ¬ ∀ (α β : ℝ) (θ μ : Fin 3 → ℝ) (c : Fin 3 → Fin 2 → ℝ), StrictMono θ →
        pcp_is_valid α β θ μ c → pcp_monotone_cost_ratio θ c → pcp_noncompetitive_venue c →
        ∀ (a a' : Fin 3 → Fin 2 → ℝ) (v v' : Fin 2 → ℝ),
          pcp_is_equilibrium α β θ μ c a v → pcp_is_equilibrium α β θ μ c a' v' → v = v' := by
  intro h
  obtain ⟨hs, hv, hm, hn, a₁, a₂, _, v₁, v₂, _, q1, q2, _, h12, _, _⟩ :=
    publication_choice_three_types_three_equilibria
  exact h12 (h _ _ _ _ _ hs hv hm hn a₁ a₂ v₁ v₂ q1 q2)
