import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EefxBundleImpApproxEfk
import AFTD.Kb.GameTheoryEconomics.IsAlphaEefxAllocation
import AFTD.Kb.GameTheoryEconomics.IsAlphaEfkAllocation
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# eefx_imp_approx_efk

Topic: fair_division   Node: 26200e03d873

Provenance: formalization of a published result. Source: arXiv:2610.34625 Lemma 3.2 -- Online Fair Division with Frequency Predictions

Let n ≥ 3 and let σ be an allocation of m goods among n agents with nonnegative additive valuations u such that every agent's bundle is nonempty. If σ is an EEFX allocation, then σ is a 1/(n-1)-EF(n-2) allocation.
-/

/-- An EEFX allocation with nonempty bundles among at least three agents with additive valuations is a 1/(n-1)-EF(n-2) allocation. -/
theorem eefx_imp_approx_efk {m n : ℕ} (hn : 3 ≤ n)
    (u : Fin n → Fin m → ℝ) (hu : ∀ i g, 0 ≤ u i g)
    (σ : Fin m → Fin n) (h_nonempty : ∀ k : Fin n, (bundle_of σ k).Nonempty)
    (h_eefx : is_alpha_eefx_allocation (fun i => additive_valuation (u i)) 1 σ) :
    is_alpha_efk_allocation (fun i => additive_valuation (u i)) (1 / ((n : ℝ) - 1)) (n - 2) σ := by
  intro i j hij
  exact eefx_bundle_imp_approx_efk hn u hu σ h_nonempty i j hij (h_eefx i)
