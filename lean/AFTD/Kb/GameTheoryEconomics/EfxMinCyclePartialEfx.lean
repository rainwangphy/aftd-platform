import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxMinCycleValue

/-!
# efx_min_cycle_partial_efx

Topic: fair_division   Node: 3fd9c7175f23

Provenance: helper lemma. Minimum-cardinality champion-cycle swap obstruction for OP-7, experiments 11442–11449; comparison with arXiv:2002.05119 Section 3.1.

Natural EFX inequalities for a possibly partial four-bundle allocation.
-/

def efx_min_cycle_partial_efx (A : Fin 4 → Finset (Fin 13)) : Prop := ∀ i j : Fin 4, i ≠ j → ∀ g ∈ A j, efx_min_cycle_value i ((A j).erase g) ≤ efx_min_cycle_value i (A i)
