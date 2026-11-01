import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxMinCycleChampion
import AFTD.Kb.GameTheoryEconomics.EfxMinCycleSubset
import AFTD.Kb.GameTheoryEconomics.EfxMinCycleSubsetComplete
import AFTD.Kb.GameTheoryEconomics.EfxMinCycleValues
import AFTD.Kb.GameTheoryEconomics.EfxMinCycleValue
import AFTD.Kb.GameTheoryEconomics.EfxNoSelfThreeSplitOld
import AFTD.Kb.GameTheoryEconomics.EfxMinCycleBaseline
import AFTD.Kb.GameTheoryEconomics.EfxMinCyclePartialEfx

/-!
# efx_min_cycle_no_self

Topic: fair_division   Node: e3f6b511c001

Provenance: helper lemma. Minimum-cardinality champion-cycle swap obstruction for OP-7, experiments 11442–11449; comparison with arXiv:2002.05119 Section 3.1.

No source self-champions, even when champion sets are allowed to be arbitrary inclusion-minimal envied subsets.
-/

theorem efx_min_cycle_no_self (i : Fin 4) (T : Finset (Fin 13)) :
  ¬ efx_min_cycle_champion i i T := by
  -- Reduce to the 16 Boolean-mask encodings of subsets of each old triple plus good 12.
  have key : ∀ (i : Fin 4) (b : Fin 4 → Bool),
      ¬ (efx_min_cycle_subset i b ⊆ insert 12 (efx_no_self_three_split_old i) ∧
        efx_min_cycle_baseline i < efx_min_cycle_value i (efx_min_cycle_subset i b) ∧
        ∀ (k : Fin 4), ∀ g ∈ efx_min_cycle_subset i b,
          efx_min_cycle_value k ((efx_min_cycle_subset i b).erase g) ≤ efx_min_cycle_baseline k) := by
    decide
  intro h
  obtain ⟨b, hb⟩ := efx_min_cycle_subset_complete i T h.1
  exact key i b (hb.symm ▸ h)
