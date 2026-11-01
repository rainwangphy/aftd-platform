import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxExistsOfTwoUniversalSmallGoods
import AFTD.Kb.GameTheoryEconomics.IsEfxGoodsEquivGoods
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# efx_exists_of_common_pair_order_even

Topic: fair_division   Node: d42a2f852a32

Provenance: helper lemma. Structural helper for efx_four_agents_additive_exists (OP-7), campaign IN-404, 2026-11-01. The baseline is universally least-good insertion for a common individual ranking in arXiv:1707.04769v3 Appendix B. Here the two new goods need not have a common order. Web searches on 2026-11-01 for two smallest goods, ordered pairs, common pair order, and EFX completion found no matching result; arXiv:2504.03951 concerns n+2 goods and does not supply this arbitrary-old-allocation preservation statement. This does not settle unrestricted four-agent EFX.

For any positive number of agents and an even number 2k of goods with nonnegative additive values, suppose every agent weakly prefers every good in an earlier consecutive pair to every good in a later pair, with arbitrary comparisons within each pair. A complete EFX allocation exists.
-/

open Function Finset

theorem efx_exists_of_common_pair_order_even (k n : ℕ) (hn : 0 < n)
    (u : Fin n → Fin (2*k) → ℝ) (hu : ∀ i g, 0 ≤ u i g)
    (horder : ∀ (i : Fin n) (g h : Fin (2*k)), g.val / 2 < h.val / 2 → u i h ≤ u i g) :
    ∃ σ : Fin (2*k) → Fin n, is_efx_goods u σ := by
  induction k with
  | zero =>
    refine ⟨fun g => Fin.elim0 g, ?_⟩
    intro i j hij g hg
    exact Fin.elim0 g
  | succ k ih =>
    have heq : 2 * (k+1) = 2*k+2 := by omega
    let e : Fin (2*(k+1)) ≃ Fin (2*k+2) := finCongr heq
    let v (i : Fin n) (g : Fin (2*k+2)) := u i (e.symm g)
    have hv (i : Fin n) (g : Fin (2*k+2)) : 0 ≤ v i g := hu i _
    have hsmall₀ (i : Fin n) (g : Fin (2*k)) :
        v i (Fin.last (2*k)).castSucc ≤ v i g.castSucc.castSucc := by
      apply horder i _ _
      change g.val / 2 < (2*k) / 2
      omega
    have hsmall₁ (i : Fin n) (g : Fin (2*k)) :
        v i (Fin.last (2*k+1)) ≤ v i g.castSucc.castSucc := by
      apply horder i _ _
      change g.val / 2 < (2*k+1) / 2
      omega
    have hold : ∃ σ : Fin (2*k) → Fin n,
        is_efx_goods (fun i g => v i g.castSucc.castSucc) σ := by
      apply ih
      · exact fun i g => hv i _
      · intro i g h hgh
        apply horder i _ _
        exact hgh
    obtain ⟨τ, hτ⟩ := efx_exists_of_two_universal_small_goods hn v hv hsmall₀ hsmall₁ hold
    refine ⟨fun g => τ (e g), ?_⟩
    have hh := (is_efx_goods_equiv_goods e v τ).mpr hτ
    simpa only [v, e.symm_apply_apply] using hh
