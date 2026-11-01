import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxMinCycleChampion
import AFTD.Kb.GameTheoryEconomics.EfxMinCycleValues
import AFTD.Kb.GameTheoryEconomics.EfxMinCycleValue
import AFTD.Kb.GameTheoryEconomics.EfxNoSelfThreeSplitOld
import AFTD.Kb.GameTheoryEconomics.EfxMinCycleBaseline
import AFTD.Kb.GameTheoryEconomics.EfxMinCyclePartialEfx

/-!
# efx_min_cycle_minimum_cardinality

Topic: fair_division   Node: 406bf2f8de13

Provenance: helper lemma. Minimum-cardinality champion-cycle swap obstruction for OP-7, experiments 11442–11449; comparison with arXiv:2002.05119 Section 3.1.

The three listed sets are inclusion-minimal envied sets with the stated champions, while every subset of at most two goods in the two relevant extensions has value at most the observer’s baseline. Consequently all three are minimum-cardinality champion sets.
-/

theorem efx_min_cycle_minimum_cardinality :
  efx_min_cycle_champion 0 1 {3,4,12} ∧
  efx_min_cycle_champion 0 1 {4,5,12} ∧
  efx_min_cycle_champion 1 0 {0,1,12} ∧
  (∀ (i : Fin 4) (g h : Fin 13), g ∈ insert 12 (efx_no_self_three_split_old 0) → h ∈ insert 12 (efx_no_self_three_split_old 0) →
    efx_min_cycle_value i {g,h} ≤ efx_min_cycle_baseline i) ∧
  (∀ (i : Fin 4) (g h : Fin 13), g ∈ insert 12 (efx_no_self_three_split_old 1) → h ∈ insert 12 (efx_no_self_three_split_old 1) →
    efx_min_cycle_value i {g,h} ≤ efx_min_cycle_baseline i) := by
  dsimp [efx_min_cycle_champion]
  decide
