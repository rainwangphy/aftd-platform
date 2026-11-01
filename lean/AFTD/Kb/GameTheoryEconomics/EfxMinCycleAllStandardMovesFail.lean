import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxMinCycleOutcome
import AFTD.Kb.GameTheoryEconomics.EfxMinCycleValues
import AFTD.Kb.GameTheoryEconomics.EfxMinCycleValue
import AFTD.Kb.GameTheoryEconomics.EfxNoSelfThreeSplitOld
import AFTD.Kb.GameTheoryEconomics.EfxMinCycleBaseline
import AFTD.Kb.GameTheoryEconomics.EfxMinCyclePartialEfx

/-!
# efx_min_cycle_all_standard_moves_fail

Topic: fair_division   Node: cc3282df34cf

Provenance: helper lemma. Minimum-cardinality champion-cycle swap obstruction for OP-7, experiments 11442–11449; comparison with arXiv:2002.05119 Section 3.1.

For each of the two two-cycle choices, the upper-half swap and either single-good lower-half repair all fail EFX despite preserving every old utility and strictly improving both cycle agents.
-/

theorem efx_min_cycle_all_standard_moves_fail :
  ∀ (c : Fin 2) (mode : Fin 3),
    ¬ efx_min_cycle_partial_efx (efx_min_cycle_outcome c mode) ∧
    (∀ i, efx_min_cycle_baseline i ≤ efx_min_cycle_value i (efx_min_cycle_outcome c mode i)) ∧
    efx_min_cycle_baseline 0 < efx_min_cycle_value 0 (efx_min_cycle_outcome c mode 0) ∧
    efx_min_cycle_baseline 1 < efx_min_cycle_value 1 (efx_min_cycle_outcome c mode 1) := by
  unfold efx_min_cycle_partial_efx
  decide
