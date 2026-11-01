import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxNondegCycleValues
import AFTD.Kb.GameTheoryEconomics.EfxNondegCycleValue
import AFTD.Kb.GameTheoryEconomics.EfxNondegCycleBaseline
import AFTD.Kb.GameTheoryEconomics.EfxMinCycleOutcome

/-!
# efx_nondeg_cycle_standard_moves_fail

Topic: fair_division   Node: 9881418d7260

Provenance: helper lemma. Nondegenerate three-source champion two-cycle exchange obstruction for OP-7, experiments 11481–11487; related arXiv:2002.05119 Section 3.1.

All six standard two-cycle swaps and one-good repairs in the nondegenerate instance are Pareto improvements but fail EFX.
-/

theorem efx_nondeg_cycle_standard_moves_fail :
  ∀ (c : Fin 2) (mode : Fin 3),
    ¬ (∀ i j : Fin 4, i ≠ j → ∀ g ∈ efx_min_cycle_outcome c mode j,
      efx_nondeg_cycle_value i ((efx_min_cycle_outcome c mode j).erase g) ≤
        efx_nondeg_cycle_value i (efx_min_cycle_outcome c mode i)) ∧
    (∀ i, efx_nondeg_cycle_baseline i ≤ efx_nondeg_cycle_value i (efx_min_cycle_outcome c mode i)) ∧
    efx_nondeg_cycle_baseline 0 < efx_nondeg_cycle_value 0 (efx_min_cycle_outcome c mode 0) ∧
    efx_nondeg_cycle_baseline 1 < efx_nondeg_cycle_value 1 (efx_min_cycle_outcome c mode 1) := by
  decide
