import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxNondegCycleChampion
import AFTD.Kb.GameTheoryEconomics.EfxNondegCycleValues
import AFTD.Kb.GameTheoryEconomics.EfxNondegCycleValue
import AFTD.Kb.GameTheoryEconomics.EfxNondegCycleBaseline
import AFTD.Kb.GameTheoryEconomics.EfxMinCycleSubset
import AFTD.Kb.GameTheoryEconomics.EfxMinCycleGoods
import AFTD.Kb.GameTheoryEconomics.EfxNoSelfThreeSplitOld

/-!
# efx_nondeg_cycle_classification

Topic: fair_division   Node: f5cc35cf5c9d

Provenance: helper lemma. Nondegenerate three-source champion two-cycle exchange obstruction for OP-7, experiments 11481–11487; related arXiv:2002.05119 Section 3.1.

The only inclusion-minimal champion two-cycle in the nondegenerate instance is 0↔1 with the two listed choices of sets.
-/

instance efx_nondeg_cycle_classification_dec (i j : Fin 4) (T : Finset (Fin 13)) :
    Decidable (efx_nondeg_cycle_champion i j T) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

lemma efx_nondeg_cycle_classification_key :
  ∀ (i j : Fin 4) (b c : Fin 4 → Bool),
    i ≠ j →
    efx_nondeg_cycle_champion i j (efx_min_cycle_subset j b) →
    efx_nondeg_cycle_champion j i (efx_min_cycle_subset i c) →
    (i = 0 ∧ j = 1 ∧
      (efx_min_cycle_subset j b = {3,4,12} ∨ efx_min_cycle_subset j b = {4,5,12}) ∧
      efx_min_cycle_subset i c = {0,1,12}) ∨
    (i = 1 ∧ j = 0 ∧ efx_min_cycle_subset j b = {0,1,12} ∧
      (efx_min_cycle_subset i c = {3,4,12} ∨ efx_min_cycle_subset i c = {4,5,12})) := by
  decide

theorem efx_nondeg_cycle_classification (i j : Fin 4) (b c : Fin 4 → Bool)
  (hij : i ≠ j)
  (hijc : efx_nondeg_cycle_champion i j (efx_min_cycle_subset j b))
  (hjic : efx_nondeg_cycle_champion j i (efx_min_cycle_subset i c)) :
  (i = 0 ∧ j = 1 ∧
    (efx_min_cycle_subset j b = {3,4,12} ∨ efx_min_cycle_subset j b = {4,5,12}) ∧
    efx_min_cycle_subset i c = {0,1,12}) ∨
  (i = 1 ∧ j = 0 ∧ efx_min_cycle_subset j b = {0,1,12} ∧
    (efx_min_cycle_subset i c = {3,4,12} ∨ efx_min_cycle_subset i c = {4,5,12})) := efx_nondeg_cycle_classification_key i j b c hij hijc hjic
