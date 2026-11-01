import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BundleOfPermuteAgents
import AFTD.Kb.GameTheoryEconomics.IsEfxGoodsAllPairs
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# is_efx_goods_permute_of_utility_le

Topic: fair_division   Node: 5b421494bd28

Provenance: helper lemma. Helper for efx_four_agents_additive_exists (OP-7), campaign session IN-404, 2026-11-01. Standard cycle elimination and ordered insertion, arXiv:1707.04769v3 Lemma 6.1 and Appendix B; no novelty claim.

A bundle permutation that weakly improves every agent's own additive value preserves EFX for nonnegative item values.
-/

open Function Finset

theorem is_efx_goods_permute_of_utility_le {m n : ℕ} (u : Fin n → Fin m → ℝ)
    (hu : ∀ i g, 0 ≤ u i g) (σ : Fin m → Fin n) (hσ : is_efx_goods u σ)
    (p : Equiv.Perm (Fin n))
    (hp : ∀ i, additive_valuation (u i) (bundle_of σ i) ≤
      additive_valuation (u i) (bundle_of σ (p i))) :
    is_efx_goods u (fun g => p.symm (σ g)) := by
  intro i j hij g hg
  simp only [bundle_of_permute_agents] at hg ⊢
  exact (is_efx_goods_all_pairs u hu σ hσ i (p j) g hg).trans (hp i)
