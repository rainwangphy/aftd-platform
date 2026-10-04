import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PcpIsEquilibrium
import AFTD.Kb.GameTheoryEconomics.PcpIsValid
import AFTD.Kb.GameTheoryEconomics.PcpMonotoneCostRatio
import AFTD.Kb.GameTheoryEconomics.PcpNoncompetitiveVenue
import AFTD.Kb.GameTheoryEconomics.PcxTheta
import AFTD.Kb.GameTheoryEconomics.PcxMu
import AFTD.Kb.GameTheoryEconomics.PcxCost
import AFTD.Kb.GameTheoryEconomics.PcxAssumptions
import AFTD.Kb.GameTheoryEconomics.PcxImpact
import AFTD.Kb.GameTheoryEconomics.PcxAction
import AFTD.Kb.GameTheoryEconomics.PcxEquilibriumOfRoot
import AFTD.Kb.GameTheoryEconomics.PcxPolyThreeRoots
import AFTD.Kb.GameTheoryEconomics.PcxImpactZeroStrictMono

/-!
# publication_choice_three_equilibria

Topic: equilibria   Node: ef284b1bf8f8

A binary-type Publication Choice Problem with two venues, alpha = 1/2, beta = 2, satisfying Assumptions 1 and 2, has three pure-strategy equilibria with pairwise different venue impacts (all publication amounts positive).
-/

/-- Counterexample to Theorem 4.1 of Wang–Wu–Xu (The Publication Choice Problem, AAAI 2026): a binary-type instance with two venues, `α = 1/2`, `β = 2`, satisfying Assumption 1 (MCR) and Assumption 2 (non-competitive venue), has three pure-strategy equilibria with pairwise different venue impacts, each with every type publishing a positive amount at every venue. -/
theorem publication_choice_three_equilibria :
    pcp_is_valid (1 / 2) 2 pcx_theta pcx_mu pcx_cost ∧ pcp_monotone_cost_ratio pcx_theta pcx_cost ∧
      pcp_noncompetitive_venue pcx_cost ∧
      ∃ (a₁ a₂ a₃ : Fin 2 → Fin 2 → ℝ) (v₁ v₂ v₃ : Fin 2 → ℝ),
        pcp_is_equilibrium (1 / 2) 2 pcx_theta pcx_mu pcx_cost a₁ v₁ ∧
        pcp_is_equilibrium (1 / 2) 2 pcx_theta pcx_mu pcx_cost a₂ v₂ ∧
        pcp_is_equilibrium (1 / 2) 2 pcx_theta pcx_mu pcx_cost a₃ v₃ ∧
        (∀ i j, 0 < a₁ i j ∧ 0 < a₂ i j ∧ 0 < a₃ i j) ∧ v₁ 0 < v₂ 0 ∧ v₂ 0 < v₃ 0 := by
  obtain ⟨hv, hm, hn⟩ := pcx_assumptions
  obtain ⟨x₁, x₂, x₃, a1, b1, a2, b2, a3, b3, e1, e2, e3⟩ := pcx_poly_three_roots
  obtain ⟨q1, p1⟩ := pcx_equilibrium_of_root x₁ (by linarith) e1
  obtain ⟨q2, p2⟩ := pcx_equilibrium_of_root x₂ (by linarith) e2
  obtain ⟨q3, p3⟩ := pcx_equilibrium_of_root x₃ (by linarith) e3
  exact ⟨hv, hm, hn, pcx_action x₁, pcx_action x₂, pcx_action x₃, pcx_impact x₁, pcx_impact x₂,
    pcx_impact x₃, q1, q2, q3, fun i j => ⟨p1 i j, p2 i j, p3 i j⟩,
    pcx_impact_zero_strictMono (by linarith) (by linarith),
    pcx_impact_zero_strictMono (by linarith) (by linarith)⟩
