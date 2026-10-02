import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MultigraphOrientationSubsidyThreeHalves
import AFTD.Kb.GameTheoryEconomics.IsOrientation
import AFTD.Kb.GameTheoryEconomics.IsGraphValuation
import AFTD.Kb.GameTheoryEconomics.IsMonotoneValuation
import AFTD.Kb.GameTheoryEconomics.HasMaxMarginalOne
import AFTD.Kb.GameTheoryEconomics.IsEnvyFreeWithSubsidy

/-!
# multigraph_orientation_subsidy_not_le_one

Topic: fair_division   Node: 5400db66d336

For three agents on a multigraph with monotone valuations, a total subsidy of n - 2 = 1 does not always suffice for an envy-free orientation, unlike simple graphs (Li-Sun-Suzuki-Xing, Thm 21).
-/

theorem multigraph_orientation_subsidy_not_le_one :
    ¬ ∀ (m : ℕ) (ends : Fin m → Fin 3 × Fin 3) (v : Fin 3 → Finset (Fin m) → ℝ),
      (∀ e, (ends e).1 ≠ (ends e).2) → is_graph_valuation ends v →
      (∀ i, is_monotone_valuation (v i) ∧ has_max_marginal_one (v i)) →
      ∃ σ p, is_orientation ends σ ∧ is_envy_free_with_subsidy v σ p ∧ ∑ i, p i ≤ 1 := by
  intro h
  obtain ⟨ends, v, hne, hg, hv, hlow, -⟩ := multigraph_orientation_subsidy_three_halves
  obtain ⟨σ, p, hσ, hef, hp⟩ := h 3 ends v hne hg hv
  linarith [hlow σ p hσ hef]
