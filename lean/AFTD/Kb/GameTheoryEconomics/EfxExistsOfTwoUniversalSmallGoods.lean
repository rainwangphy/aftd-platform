import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxExistsOfTwoUniversalSmallGoodsIr
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# efx_exists_of_two_universal_small_goods

Topic: fair_division   Node: 36bccb237e13

Provenance: helper lemma. Structural helper for efx_four_agents_additive_exists (OP-7), campaign IN-404, 2026-11-01.

For a positive number of agents with nonnegative real additive values, suppose each of the last two goods is weakly less valuable to every agent than each old good, and a complete EFX allocation of the old goods exists. Then a complete EFX allocation including both new goods exists.
-/

open Function Finset

theorem efx_exists_of_two_universal_small_goods {m n : ℕ} (hn : 0 < n)
    (u : Fin n → Fin (m+2) → ℝ) (hu : ∀ i g, 0 ≤ u i g)
    (hsmall₀ : ∀ (i : Fin n) (g : Fin m), u i (Fin.last m).castSucc ≤ u i g.castSucc.castSucc)
    (hsmall₁ : ∀ (i : Fin n) (g : Fin m), u i (Fin.last (m+1)) ≤ u i g.castSucc.castSucc)
    (h : ∃ σ : Fin m → Fin n, is_efx_goods (fun i g => u i g.castSucc.castSucc) σ) :
    ∃ τ : Fin (m+2) → Fin n, is_efx_goods u τ := by
  obtain ⟨σ, hσ⟩ := h
  obtain ⟨τ, hτ, _, _⟩ := efx_exists_of_two_universal_small_goods_ir hn u hu hsmall₀ hsmall₁ σ hσ
  exact ⟨τ, hτ⟩
