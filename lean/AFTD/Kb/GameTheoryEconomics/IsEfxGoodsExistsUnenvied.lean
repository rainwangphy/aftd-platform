import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.FiniteUnenviedPermutation
import AFTD.Kb.GameTheoryEconomics.BundleOfPermuteAgents
import AFTD.Kb.GameTheoryEconomics.IsEfxGoodsPermuteOfUtilityLe
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# is_efx_goods_exists_unenvied

Topic: fair_division   Node: 113ff8fd9353

Provenance: helper lemma. Helper for efx_four_agents_additive_exists (OP-7), campaign session IN-404, 2026-11-01. Standard cycle elimination and ordered insertion, arXiv:1707.04769v3 Lemma 6.1 and Appendix B; no novelty claim.

For a positive number of agents, any EFX allocation of nonnegative additive goods can be changed to another EFX allocation that weakly improves every own utility and has an unenvied agent.
-/

open Function Finset

theorem is_efx_goods_exists_unenvied {m n : ℕ} (hn : 0 < n) (u : Fin n → Fin m → ℝ)
    (hu : ∀ i g, 0 ≤ u i g) (σ : Fin m → Fin n) (hσ : is_efx_goods u σ) :
    ∃ τ : Fin m → Fin n, is_efx_goods u τ ∧
      (∀ i, additive_valuation (u i) (bundle_of σ i) ≤
        additive_valuation (u i) (bundle_of τ i)) ∧
      ∃ s : Fin n, ∀ i, additive_valuation (u i) (bundle_of τ s) ≤
        additive_valuation (u i) (bundle_of τ i) := by
  classical
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  obtain ⟨p, hp, s, hs⟩ := finite_unenvied_permutation
    (fun i j => additive_valuation (u i) (bundle_of σ j))
  refine ⟨fun g => p.symm (σ g), is_efx_goods_permute_of_utility_le u hu σ hσ p hp, ?_, s, ?_⟩
  · simpa only [bundle_of_permute_agents] using hp
  · simpa only [bundle_of_permute_agents] using hs
