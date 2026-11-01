import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxThreeSplitValues
import AFTD.Kb.GameTheoryEconomics.IsEfxGoodsNatCastIff
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# efx_three_split_sanity

Topic: fair_division   Node: 5b32b93d1348

Provenance: helper lemma. Finite equal-pair obstruction to OP-7 completion routes, experiments 11408, 11409, 11411, 11412.

All values are positive. In the initial partial allocation (0,0,1,1,2,2,3,3), each agent values all four old bundles equally, values the unallocated ninth good no more than her own bundle, and the allocation is EFX. The complete allocation (0,0,1,3,1,2,0,2,3) is EFX.
-/

theorem efx_three_split_sanity :
  (∀ i g, 0 < efx_three_split_values i g) ∧
  (∀ (i j : Fin 4),
    additive_valuation (fun g : Fin 8 => (efx_three_split_values i g.castSucc : ℝ))
      (bundle_of ![(0 : Fin 4),0,1,1,2,2,3,3] j) =
    additive_valuation (fun g : Fin 8 => (efx_three_split_values i g.castSucc : ℝ))
      (bundle_of ![(0 : Fin 4),0,1,1,2,2,3,3] i)) ∧
  (∀ i : Fin 4, (efx_three_split_values i 8 : ℝ) ≤
    additive_valuation (fun g : Fin 8 => (efx_three_split_values i g.castSucc : ℝ))
      (bundle_of ![(0 : Fin 4),0,1,1,2,2,3,3] i)) ∧
  is_efx_goods (fun i (g : Fin 8) => (efx_three_split_values i g.castSucc : ℝ))
    ![(0 : Fin 4),0,1,1,2,2,3,3] ∧
  is_efx_goods (fun i g => (efx_three_split_values i g : ℝ))
    ![(0 : Fin 4),0,1,3,1,2,0,2,3] := by
  refine ⟨by decide +kernel, ?_, ?_, ?_, ?_⟩
  · have h : ∀ (i j : Fin 4),
        (∑ g ∈ bundle_of ![(0 : Fin 4),0,1,1,2,2,3,3] j, efx_three_split_values i g.castSucc) =
        (∑ g ∈ bundle_of ![(0 : Fin 4),0,1,1,2,2,3,3] i, efx_three_split_values i g.castSucc) := by
      decide +kernel
    intro i j
    dsimp [additive_valuation]
    exact_mod_cast h i j
  · have h : ∀ i : Fin 4, efx_three_split_values i 8 ≤
        (∑ g ∈ bundle_of ![(0 : Fin 4),0,1,1,2,2,3,3] i, efx_three_split_values i g.castSucc) := by
      decide +kernel
    intro i
    dsimp [additive_valuation]
    exact_mod_cast h i
  · apply (is_efx_goods_nat_cast_iff (fun i (g : Fin 8) => efx_three_split_values i g.castSucc) _).mpr
    decide +kernel
  · apply (is_efx_goods_nat_cast_iff (fun i (g : Fin 9) => efx_three_split_values i g) _).mpr
    decide +kernel
