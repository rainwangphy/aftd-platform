import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxMinCycleValues
import AFTD.Kb.GameTheoryEconomics.EfxNondegCycleExponents

/-!
# efx_nondeg_cycle_values

Topic: fair_division   Node: dee36bcf44e8

Provenance: helper lemma. Nondegenerate three-source champion two-cycle exchange obstruction for OP-7, experiments 11481–11487; related arXiv:2002.05119 Section 3.1.

The nondegenerate perturbation of the minimum-cardinality champion-cycle matrix.
-/

def efx_nondeg_cycle_values : Fin 4 → Fin 13 → ℕ := fun i g => 16384 * efx_min_cycle_values i g + 2 ^ efx_nondeg_cycle_exponents i g
