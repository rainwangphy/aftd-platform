import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxMinCycleValues
import AFTD.Kb.GameTheoryEconomics.EfxMinCycleValue
import AFTD.Kb.GameTheoryEconomics.EfxNoSelfThreeSplitOld
import AFTD.Kb.GameTheoryEconomics.EfxMinCycleBaseline
import AFTD.Kb.GameTheoryEconomics.EfxMinCyclePartialEfx

/-!
# efx_min_cycle_sanity

Topic: fair_division   Node: 6a4fe92283c4

Provenance: helper lemma. Minimum-cardinality champion-cycle swap obstruction for OP-7, experiments 11442–11449; comparison with arXiv:2002.05119 Section 3.1.

Every value is positive; each agent values all old bundles equally, values each good of her own old bundle at least as much as good 12, and each old bundle has a good that some foreign agent values less than good 12. The old partial allocation is EFX.
-/

theorem efx_min_cycle_sanity :
  (∀ i g, 0 < efx_min_cycle_values i g) ∧
  (∀ i j, efx_min_cycle_value i (efx_no_self_three_split_old j) = efx_min_cycle_baseline i) ∧
  (∀ i g, g ∈ efx_no_self_three_split_old i → efx_min_cycle_values i 12 ≤ efx_min_cycle_values i g) ∧
  (∀ j, ∃ i : Fin 4, i ≠ j ∧ ∃ g ∈ efx_no_self_three_split_old j, efx_min_cycle_values i g < efx_min_cycle_values i 12) ∧
  efx_min_cycle_partial_efx efx_no_self_three_split_old := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i g
    fin_cases i <;> fin_cases g <;> decide
  · intro i j
    fin_cases i <;> fin_cases j <;> decide
  · intro i g hg
    fin_cases i <;> fin_cases g <;>
      simp_all [efx_no_self_three_split_old, efx_min_cycle_values]
  · intro j
    fin_cases j <;> decide
  · intro i j hij g hg
    fin_cases i <;> fin_cases j <;> fin_cases g <;>
      simp_all [efx_min_cycle_value, efx_no_self_three_split_old, efx_min_cycle_values] <;>
      decide
