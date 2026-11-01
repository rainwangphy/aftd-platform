import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxExistsOfCommonPairOrderEven
import AFTD.Kb.GameTheoryEconomics.EfxExistsOfCommonPairOrderOdd
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods

/-!
# efx_exists_of_common_pair_order

Topic: fair_division   Node: 85a3a3270ebc

Provenance: helper lemma. Structural helper for efx_four_agents_additive_exists (OP-7), campaign IN-404, 2026-11-01. The baseline is universally least-good insertion for a common individual ranking in arXiv:1707.04769v3 Appendix B. Here the two new goods need not have a common order. Web searches on 2026-11-01 for two smallest goods, ordered pairs, common pair order, and EFX completion found no matching result; arXiv:2504.03951 concerns n+2 goods and does not supply this arbitrary-old-allocation preservation statement. This does not settle unrestricted four-agent EFX.

For any finite number m of goods, any positive number n of agents, and nonnegative real additive values, suppose for every agent and goods g,h, floor(g.index/2) < floor(h.index/2) implies that the value of h is at most the value of g. A complete EFX allocation exists. Thus all agents agree on the order of consecutive blocks of at most two goods, but can disagree on comparisons within each pair.
-/

open Function Finset

theorem efx_exists_of_common_pair_order (m n : ℕ) (hn : 0 < n)
    (u : Fin n → Fin m → ℝ) (hu : ∀ i g, 0 ≤ u i g)
    (horder : ∀ (i : Fin n) (g h : Fin m), g.val / 2 < h.val / 2 → u i h ≤ u i g) :
    ∃ σ : Fin m → Fin n, is_efx_goods u σ := by
  have hex : (∃ k, m = 2*k) ∨ (∃ k, m = 2*k+1) := by
    by_cases hm : m % 2 = 0
    · exact Or.inl ⟨m / 2, by omega⟩
    · exact Or.inr ⟨m / 2, by omega⟩
  rcases hex with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · exact efx_exists_of_common_pair_order_even k n hn u hu horder
  · exact efx_exists_of_common_pair_order_odd k n hn u hu horder
