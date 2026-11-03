import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsFractionallyParetoOptimal
import AFTD.Kb.GameTheoryEconomics.IsEnvyFreeWithSubsidy
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods
import AFTD.Kb.GameTheoryEconomics.IsFractionallyParetoOptimalZeroGoods
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# scaled_common_ratio_bivalued_efx_fpo_envyfreeable_zero_goods

Topic: fair_division   Node: befb63cf20d9

Provenance: helper lemma. step towards scaled_common_ratio_bivalued_efx_fpo_envyfreeable

When m = 0, the empty allocation Fin.elim0 and zero subsidy vector 0 satisfy EFX, envy-freeness with subsidies, and fractional Pareto optimality.
-/

/-- For zero indivisible goods, the empty allocation with zero subsidies is EFX, envy-free with subsidies, and fractionally Pareto optimal. -/
theorem scaled_common_ratio_bivalued_efx_fpo_envyfreeable_zero_goods
    (n : ℕ) (hn : 2 ≤ n)
    (r : ℝ) (hr : 1 < r)
    (a : Fin n → ℝ) (ha : ∀ i, 0 < a i)
    (v : Fin n → Fin 0 → ℝ) (hv : ∀ i g, v i g = a i ∨ v i g = r * a i) :
    ∃ (σ : Fin 0 → Fin n) (s : Fin n → ℝ),
      is_efx_goods v σ ∧
      is_envy_free_with_subsidy (fun i => additive_valuation (v i)) σ s ∧
      is_fractionally_pareto_optimal v σ := by
  refine ⟨Fin.elim0, fun _ => 0, ?_, ?_, ?_⟩
  · intro i j hij g hg
    simp [bundle_of] at hg
  · simp [is_envy_free_with_subsidy, additive_valuation, bundle_of]
  · exact is_fractionally_pareto_optimal_zero_goods n v Fin.elim0
