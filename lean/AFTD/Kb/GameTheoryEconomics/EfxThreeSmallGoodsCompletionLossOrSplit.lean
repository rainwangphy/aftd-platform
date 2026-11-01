import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxThreeSmallGoodsObstructionValues
import AFTD.Kb.GameTheoryEconomics.EfxThreeSmallGoodsObstructionCoarse
import AFTD.Kb.GameTheoryEconomics.EfxThreeSmallGoodsObstructionThreshold
import AFTD.Kb.GameTheoryEconomics.EfxThreeSmallGoodsObstructionNoCurrentIr
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# efx_three_small_goods_completion_loss_or_split

Topic: fair_division   Node: a9824cd1c3d4

Provenance: helper lemma. Route obstruction for efx_four_agents_additive_exists (OP-7), campaign IN-404, 2026-11-01. Experiments 11265, 11268, and 11269. The last independently exhausts all 16384 full coarse assignments and all 1152 old-permutation two-bonus states; a row scaling removes a welfare-maximizer tie. General Pareto-monotone EFX completion barriers are already known in arXiv:2002.05119v3 Section 5. This explicit three-universally-small-goods example constrains maximum-sum two-bonus completion, not EFX existence or the original-diagonal three-bonus conjecture, and carries no research-level novelty claim.

In the explicit eleven-good instance cast to real values, every complete EFX allocation which keeps each of the four old adjacent pairs intact has some agent whose utility is strictly less than her starting ten-good EFX utility threshold. Thus a completion preserving all current utilities must split an old pair.
-/

open Function Finset

theorem efx_three_small_goods_completion_loss_or_split (σ : Fin 11 → Fin 4)
    (hEF : is_efx_goods (fun i g => (efx_three_small_goods_obstruction_values i g : ℝ)) σ)
    (hstay : σ 0 = σ 1 ∧ σ 2 = σ 3 ∧ σ 4 = σ 5 ∧ σ 6 = σ 7) :
    ∃ i : Fin 4, additive_valuation (fun g => (efx_three_small_goods_obstruction_values i g : ℝ))
      (bundle_of σ i) < (efx_three_small_goods_obstruction_threshold i : ℝ) := by
  rcases hstay with ⟨h0,h1,h2,h3⟩
  let p : Fin 7 → Fin 4 := ![σ 0,σ 2,σ 4,σ 6,σ 8,σ 9,σ 10]
  have heq : σ = efx_three_small_goods_obstruction_coarse p := by
    funext g
    fin_cases g <;> simp [p, efx_three_small_goods_obstruction_coarse, h0, h1, h2, h3]
  rw [heq] at hEF ⊢
  exact efx_three_small_goods_obstruction_no_current_ir p hEF
