import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxExistsOfUniversalLeastGood
import AFTD.Kb.GameTheoryEconomics.EfxExistsOfCommonPairOrderEven
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods

/-!
# efx_exists_of_common_pair_order_odd

Topic: fair_division   Node: 32924f46f31f

Provenance: helper lemma. Structural helper for efx_four_agents_additive_exists (OP-7), campaign IN-404, 2026-11-01. The baseline is universally least-good insertion for a common individual ranking in arXiv:1707.04769v3 Appendix B. Here the two new goods need not have a common order. Web searches on 2026-11-01 for two smallest goods, ordered pairs, common pair order, and EFX completion found no matching result; arXiv:2504.03951 concerns n+2 goods and does not supply this arbitrary-old-allocation preservation statement. This does not settle unrestricted four-agent EFX.

For any positive number of agents and 2k+1 nonnegative additive goods, suppose every agent weakly prefers goods with smaller floor(index/2) to those with larger floor(index/2), with no required order within a pair. A complete EFX allocation exists; the last block is a singleton.
-/

open Function Finset

theorem efx_exists_of_common_pair_order_odd (k n : ℕ) (hn : 0 < n)
    (u : Fin n → Fin (2*k+1) → ℝ) (hu : ∀ i g, 0 ≤ u i g)
    (horder : ∀ (i : Fin n) (g h : Fin (2*k+1)), g.val / 2 < h.val / 2 → u i h ≤ u i g) :
    ∃ σ : Fin (2*k+1) → Fin n, is_efx_goods u σ := by
  apply efx_exists_of_universal_least_good hn u hu
  · intro i g
    apply horder i _ _
    change g.val / 2 < (2*k) / 2
    omega
  · apply efx_exists_of_common_pair_order_even k n hn
    · exact fun i g => hu i _
    · intro i g h hgh
      apply horder i _ _
      exact hgh
