import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxNoSelfThreeSplitOld
import AFTD.Kb.GameTheoryEconomics.EfxMinCycleBaseline
import AFTD.Kb.GameTheoryEconomics.EfxMinCycleValue

/-!
# efx_min_cycle_champion

Topic: fair_division   Node: 3fb87d062a3b

Provenance: helper lemma. Minimum-cardinality champion-cycle swap obstruction for OP-7, experiments 11442–11449; comparison with arXiv:2002.05119 Section 3.1.

An inclusion-minimal envied set T in the extension of old bundle j: agent i strictly prefers it and no agent prefers it after any deletion.
-/

def efx_min_cycle_champion (i j : Fin 4) (T : Finset (Fin 13)) : Prop := T ⊆ insert 12 (efx_no_self_three_split_old j) ∧
  efx_min_cycle_baseline i < efx_min_cycle_value i T ∧
  ∀ (k : Fin 4) (g : Fin 13), g ∈ T → efx_min_cycle_value k (T.erase g) ≤ efx_min_cycle_baseline k
