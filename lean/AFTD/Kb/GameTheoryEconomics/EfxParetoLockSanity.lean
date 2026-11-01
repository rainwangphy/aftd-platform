import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxParetoLockValues
import AFTD.Kb.GameTheoryEconomics.EfxParetoLockBaseline
import AFTD.Kb.GameTheoryEconomics.EfxParetoLockUtility
import AFTD.Kb.GameTheoryEconomics.EfxParetoLockFeasible
import AFTD.Kb.GameTheoryEconomics.IsEfxGoodsNatCastIff
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# efx_pareto_lock_sanity

Topic: fair_division   Node: a9ba73a9becd

Provenance: helper lemma. Four-agent locked-good lift of the partial EFX Pareto barrier in arXiv:2002.05119, Section 5; experiments 11454–11457.

All values are positive. The partial allocation (1,0,0,0,1,2,4,3), where 4 means unallocated, is EFX and meets the baseline utilities; the unallocated good 6 is worth no more than each baseline. The complete allocation (0,0,0,1,1,2,2,3) is EFX.
-/

theorem efx_pareto_lock_sanity :
  (∀ i g, 0 < efx_pareto_lock_values i g) ∧
  efx_pareto_lock_feasible ![(1 : Fin 5),0,0,0,1,2,4,3] ∧
  (∀ i : Fin 4, efx_pareto_lock_values i 6 ≤ efx_pareto_lock_baseline i) ∧
  is_efx_goods (fun i g => (efx_pareto_lock_values i g : ℝ))
    ![(0 : Fin 4),0,0,1,1,2,2,3] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · decide
  · unfold efx_pareto_lock_feasible efx_pareto_lock_utility
    decide
  · decide
  · rw [is_efx_goods_nat_cast_iff]
    decide
