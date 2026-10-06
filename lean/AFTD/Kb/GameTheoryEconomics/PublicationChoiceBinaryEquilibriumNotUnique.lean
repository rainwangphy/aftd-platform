import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PcpIsEquilibrium
import AFTD.Kb.GameTheoryEconomics.PcpIsValid
import AFTD.Kb.GameTheoryEconomics.PcpMonotoneCostRatio
import AFTD.Kb.GameTheoryEconomics.PcpNoncompetitiveVenue
import AFTD.Kb.GameTheoryEconomics.PublicationChoiceThreeEquilibria

/-!
# publication_choice_binary_equilibrium_not_unique

Topic: equilibria   Node: 500588ac1693

Provenance: erratum. Corrects: The Publication Choice Problem, AAAI 2026 (arXiv:2511.13678v2), Theorem 4.1 (a binary-type problem satisfying the standing assumptions and Assumptions 1-2 has a unique pure-strategy equilibrium): false; counterexample alpha = 1/2, beta = 2, two venues, types (1, 8), three equilibria

Theorem 4.1 of arXiv:2511.13678 is false: not every binary-type Publication Choice Problem satisfying the standing assumptions, Assumption 1 and Assumption 2 has a unique pure-strategy equilibrium.
-/

/-- Theorem 4.1 of arXiv:2511.13678 is false: not every binary-type Publication Choice Problem satisfying the standing assumptions, Assumption 1 (MCR) and Assumption 2 (non-competitive venue) has a unique pure-strategy equilibrium, even counting only the venue impacts. -/
theorem publication_choice_binary_equilibrium_not_unique :
    ¬ ∀ (α β : ℝ) (θ μ : Fin 2 → ℝ) (c : Fin 2 → Fin 2 → ℝ),
        pcp_is_valid α β θ μ c → pcp_monotone_cost_ratio θ c → pcp_noncompetitive_venue c →
        ∀ (a a' : Fin 2 → Fin 2 → ℝ) (v v' : Fin 2 → ℝ),
          pcp_is_equilibrium α β θ μ c a v → pcp_is_equilibrium α β θ μ c a' v' → v = v' := by
  intro h
  obtain ⟨hv, hm, hn, a₁, a₂, _, v₁, v₂, _, q1, q2, _, _, h12, _⟩ := publication_choice_three_equilibria
  have := h _ _ _ _ _ hv hm hn a₁ a₂ v₁ v₂ q1 q2
  rw [this] at h12
  exact lt_irrefl _ h12
