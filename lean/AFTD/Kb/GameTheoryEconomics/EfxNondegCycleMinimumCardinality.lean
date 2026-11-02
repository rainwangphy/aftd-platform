import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxNondegCycleChampion
import AFTD.Kb.GameTheoryEconomics.EfxNondegCycleValues
import AFTD.Kb.GameTheoryEconomics.EfxNondegCycleValue
import AFTD.Kb.GameTheoryEconomics.EfxNondegCycleBaseline
import AFTD.Kb.GameTheoryEconomics.EfxNoSelfThreeSplitOld
import AFTD.Kb.GameTheoryEconomics.EfxNondegCycleClassification

/-!
# efx_nondeg_cycle_minimum_cardinality

Topic: fair_division   Node: d315f62a9156

Provenance: helper lemma. Nondegenerate minimum-cardinality champion check, experiment 11482; related arXiv:2002.05119 Section 3.1.

The three selected inclusion-minimal champion sets have size three, and no subset of at most two goods in either target extension is envied by any agent; thus these are minimum-cardinality champions.
-/

theorem efx_nondeg_cycle_minimum_cardinality :
  efx_nondeg_cycle_champion 0 1 {3,4,12} ∧
  efx_nondeg_cycle_champion 0 1 {4,5,12} ∧
  efx_nondeg_cycle_champion 1 0 {0,1,12} ∧
  (∀ (i : Fin 4) (g h : Fin 13), g ∈ insert 12 (efx_no_self_three_split_old 0) → h ∈ insert 12 (efx_no_self_three_split_old 0) →
    efx_nondeg_cycle_value i {g,h} ≤ efx_nondeg_cycle_baseline i) ∧
  (∀ (i : Fin 4) (g h : Fin 13), g ∈ insert 12 (efx_no_self_three_split_old 1) → h ∈ insert 12 (efx_no_self_three_split_old 1) →
    efx_nondeg_cycle_value i {g,h} ≤ efx_nondeg_cycle_baseline i) := by
  decide
