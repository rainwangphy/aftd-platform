import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxNoSelfThreeSplitOld
import AFTD.Kb.GameTheoryEconomics.EfxNondegCycleBaseline
import AFTD.Kb.GameTheoryEconomics.EfxNondegCycleValue

/-!
# efx_nondeg_cycle_champion

Topic: fair_division   Node: bbcaa5445abf

Provenance: helper lemma. Nondegenerate three-source champion two-cycle exchange obstruction for OP-7, experiments 11481–11487; related arXiv:2002.05119 Section 3.1.

An inclusion-minimal envied set for the nondegenerate cycle instance.
-/

def efx_nondeg_cycle_champion (i j : Fin 4) (T : Finset (Fin 13)) : Prop := T ⊆ insert 12 (efx_no_self_three_split_old j) ∧
  efx_nondeg_cycle_baseline i < efx_nondeg_cycle_value i T ∧
  ∀ (k : Fin 4) (g : Fin 13), g ∈ T → efx_nondeg_cycle_value k (T.erase g) ≤ efx_nondeg_cycle_baseline k
