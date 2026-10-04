import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PcpIsEquilibrium
import AFTD.Kb.GameTheoryEconomics.PcpIsValid
import AFTD.Kb.GameTheoryEconomics.PcpMonotoneCostRatio
import AFTD.Kb.GameTheoryEconomics.PcpNoncompetitiveVenue
import AFTD.Kb.GameTheoryEconomics.PcpHalfTwoAction
import AFTD.Kb.GameTheoryEconomics.PcpTwoVenueEquilibriumOfFixedPoint
import AFTD.Kb.GameTheoryEconomics.PcyTheta
import AFTD.Kb.GameTheoryEconomics.PcyMu
import AFTD.Kb.GameTheoryEconomics.PcyCost
import AFTD.Kb.GameTheoryEconomics.PcyAssumptions
import AFTD.Kb.GameTheoryEconomics.PcyImpact
import AFTD.Kb.GameTheoryEconomics.PcyPoly
import AFTD.Kb.GameTheoryEconomics.PcyFixedPointOfRoot
import AFTD.Kb.GameTheoryEconomics.PcyPolyThreeRoots

/-!
# publication_choice_three_types_three_equilibria

Topic: equilibria   Node: e1371c6c392c

A Publication Choice Problem with three strictly ordered types and two venues, alpha = 1/2, beta = 2, satisfying Assumptions 1 and 2, has three pure-strategy equilibria with pairwise different venue impacts.
-/

/-- Counterexample to Conjecture 4.2 of Wang–Wu–Xu (uniqueness of equilibrium with many types): a three-type instance with strictly increasing types, two venues, `α = 1/2`, `β = 2`, satisfying Assumption 1 (MCR) and Assumption 2 (non-competitive venue), has three pure-strategy equilibria with pairwise different venue impacts. -/
theorem publication_choice_three_types_three_equilibria :
    StrictMono pcy_theta ∧ pcp_is_valid (1 / 2) 2 pcy_theta pcy_mu pcy_cost ∧
      pcp_monotone_cost_ratio pcy_theta pcy_cost ∧ pcp_noncompetitive_venue pcy_cost ∧
      ∃ (a₁ a₂ a₃ : Fin 3 → Fin 2 → ℝ) (v₁ v₂ v₃ : Fin 2 → ℝ),
        pcp_is_equilibrium (1 / 2) 2 pcy_theta pcy_mu pcy_cost a₁ v₁ ∧
        pcp_is_equilibrium (1 / 2) 2 pcy_theta pcy_mu pcy_cost a₂ v₂ ∧
        pcp_is_equilibrium (1 / 2) 2 pcy_theta pcy_mu pcy_cost a₃ v₃ ∧
        v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃ := by
  obtain ⟨hs, hv, hm, hn⟩ := pcy_assumptions
  have hc : ∀ i j, 0 < pcy_cost i j := hv.2.2.2.2.2.1
  obtain ⟨y₁, y₂, y₃, a1, b1, a2, b2, a3, b3, e1, e2, e3⟩ := pcy_poly_three_roots
  have key : ∀ y, 0 < y → pcy_poly y = 0 →
      pcp_is_equilibrium (1 / 2) 2 pcy_theta pcy_mu pcy_cost
        (pcp_half_two_action pcy_cost ![pcy_impact y 0, pcy_impact y 1]) ![pcy_impact y 0, pcy_impact y 1] ∧
      0 < pcy_impact y 0 ∧ pcy_impact y 1 = y * pcy_impact y 0 := by
    intro y hy hP
    obtain ⟨h0, hf⟩ := pcy_fixed_point_of_root y hy
    exact ⟨pcp_two_venue_equilibrium_of_fixed_point _ _ _ hc y h0 (hf hP), h0, hf hP⟩
  obtain ⟨q1, p1, f1⟩ := key y₁ (by linarith) e1
  obtain ⟨q2, p2, f2⟩ := key y₂ (by linarith) e2
  obtain ⟨q3, p3, f3⟩ := key y₃ (by linarith) e3
  have hne : ∀ y y', 0 < pcy_impact y 0 → pcy_impact y 1 = y * pcy_impact y 0 →
      pcy_impact y' 1 = y' * pcy_impact y' 0 → y ≠ y' →
      (![pcy_impact y 0, pcy_impact y 1] : Fin 2 → ℝ) ≠ ![pcy_impact y' 0, pcy_impact y' 1] := by
    intro y y' h0 hf hf' hyy heq
    have e0 : pcy_impact y 0 = pcy_impact y' 0 := by simpa using congrFun heq 0
    have e1 : pcy_impact y 1 = pcy_impact y' 1 := by simpa using congrFun heq 1
    apply hyy
    have : y * pcy_impact y 0 = y' * pcy_impact y 0 := by rw [← hf, e1, hf', e0]
    exact mul_right_cancel₀ h0.ne' this
  exact ⟨hs, hv, hm, hn, _, _, _, _, _, _, q1, q2, q3,
    hne _ _ p1 f1 f2 (by intro h; linarith), hne _ _ p1 f1 f3 (by intro h; linarith),
    hne _ _ p2 f2 f3 (by intro h; linarith)⟩
