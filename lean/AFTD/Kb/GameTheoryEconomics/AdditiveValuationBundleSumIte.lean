import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# additive_valuation_bundle_sum_ite

Topic: fair_division   Node: 4a459b2d8c8a

Provenance: helper lemma. Helper for efx_four_agents_additive_exists (OP-7), campaign session IN-404, 2026-11-01.

An additive value of an allocated bundle equals the sum over all goods of the item value when that good has the specified owner, and zero otherwise.
-/

open Function Finset

theorem additive_valuation_bundle_sum_ite {m n : ℕ} (u : Fin m → ℝ) (σ : Fin m → Fin n) (i : Fin n) :
    additive_valuation u (bundle_of σ i) = ∑ g, if σ g = i then u g else 0 := by
  simp [additive_valuation, bundle_of, Finset.sum_filter]
