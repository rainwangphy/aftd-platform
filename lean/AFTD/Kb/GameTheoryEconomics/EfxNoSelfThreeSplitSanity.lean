import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxNoSelfThreeSplitValues
import AFTD.Kb.GameTheoryEconomics.EfxNoSelfThreeSplitValue
import AFTD.Kb.GameTheoryEconomics.EfxNoSelfThreeSplitOld
import AFTD.Kb.GameTheoryEconomics.EfxNoSelfThreeSplitBaseline
import AFTD.Kb.GameTheoryEconomics.IsEfxGoodsNatCastIff
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# efx_no_self_three_split_sanity

Topic: fair_division   Node: 91562669251e

Provenance: helper lemma. Positive equal-triple no-self-champion obstruction to the OP-7 two-bundle exchange route, experiments 11462–11471.

The matrix is positive; each agent values every old triple equally at her baseline, values every good in her own triple at least as much as charity, and each triple has a good that some foreign agent values below charity. The initial partial allocation is EFX.
-/

theorem efx_no_self_three_split_sanity :
  (∀ i g, 0 < efx_no_self_three_split_values i g) ∧
  (∀ i j, efx_no_self_three_split_value i (efx_no_self_three_split_old j) = efx_no_self_three_split_baseline i) ∧
  (∀ i g, g ∈ efx_no_self_three_split_old i → efx_no_self_three_split_values i 12 ≤ efx_no_self_three_split_values i g) ∧
  (∀ j, ∃ i : Fin 4, i ≠ j ∧ ∃ g ∈ efx_no_self_three_split_old j,
      efx_no_self_three_split_values i g < efx_no_self_three_split_values i 12) ∧
  is_efx_goods (fun i (g : Fin 12) => (efx_no_self_three_split_values i g.castSucc : ℝ))
    ![(0 : Fin 4),0,0,1,1,1,2,2,2,3,3,3] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide
  · rw [is_efx_goods_nat_cast_iff]
    decide
