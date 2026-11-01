import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxNondegCycleChampion
import AFTD.Kb.GameTheoryEconomics.EfxMinCycleSubset
import AFTD.Kb.GameTheoryEconomics.EfxMinCycleSubsetComplete
import AFTD.Kb.GameTheoryEconomics.EfxNondegCycleValues
import AFTD.Kb.GameTheoryEconomics.EfxNondegCycleValue
import AFTD.Kb.GameTheoryEconomics.EfxNondegCycleBaseline
import AFTD.Kb.GameTheoryEconomics.EfxNoSelfThreeSplitOld

/-!
# efx_nondeg_cycle_no_self

Topic: fair_division   Node: 158e3da16e6a

Provenance: helper lemma. Nondegenerate three-source champion two-cycle exchange obstruction for OP-7, experiments 11481–11487; related arXiv:2002.05119 Section 3.1.

No agent has an inclusion-minimal self-champion set in the nondegenerate cycle instance.
-/

theorem efx_nondeg_cycle_no_self (i : Fin 4) (T : Finset (Fin 13)) :
  ¬ efx_nondeg_cycle_champion i i T := by
  have key : ∀ (i : Fin 4) (b : Fin 4 → Bool),
      ¬ (efx_min_cycle_subset i b ⊆ insert 12 (efx_no_self_three_split_old i) ∧
        efx_nondeg_cycle_baseline i < efx_nondeg_cycle_value i (efx_min_cycle_subset i b) ∧
        ∀ (k : Fin 4), ∀ g ∈ efx_min_cycle_subset i b,
          efx_nondeg_cycle_value k ((efx_min_cycle_subset i b).erase g) ≤ efx_nondeg_cycle_baseline k) := by
    decide
  intro h
  obtain ⟨b, hb⟩ := efx_min_cycle_subset_complete i T h.1
  exact key i b (hb.symm ▸ h)
