import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsEfxGoodsInsertOfUnenviedOfMin
import AFTD.Kb.GameTheoryEconomics.IsEfxGoodsExistsUnenvied
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# efx_exists_of_universal_least_good

Topic: fair_division   Node: f811b8aa45dd

Provenance: helper lemma. Helper for efx_four_agents_additive_exists (OP-7), campaign session IN-404, 2026-11-01. Standard cycle elimination and ordered insertion, arXiv:1707.04769v3 Lemma 6.1 and Appendix B; no novelty claim.

For a positive number of agents and nonnegative additive values, if the last good is weakly least valuable for every agent, existence of EFX without it implies existence of EFX with it.
-/

open Function Finset

theorem efx_exists_of_universal_least_good {m n : ℕ} (hn : 0 < n)
    (u : Fin n → Fin (m+1) → ℝ) (hu : ∀ i g, 0 ≤ u i g)
    (hmin : ∀ (i : Fin n) (g : Fin m), u i (Fin.last m) ≤ u i g.castSucc)
    (h : ∃ σ : Fin m → Fin n, is_efx_goods (fun i g => u i g.castSucc) σ) :
    ∃ τ : Fin (m+1) → Fin n, is_efx_goods u τ := by
  obtain ⟨σ, hσ⟩ := h
  obtain ⟨τ, hτ, _, s, hs⟩ := is_efx_goods_exists_unenvied hn
    (fun i g => u i g.castSucc) (fun i g => hu i g.castSucc) σ hσ
  exact ⟨Fin.lastCases s τ, is_efx_goods_insert_of_unenvied_of_min u hu τ hτ s hs (fun i _ g _ => hmin i g)⟩
