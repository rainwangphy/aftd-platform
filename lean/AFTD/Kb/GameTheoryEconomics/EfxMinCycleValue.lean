import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxMinCycleValues

/-!
# efx_min_cycle_value

Topic: fair_division   Node: 6fe95e2afab0

Provenance: helper lemma. Minimum-cardinality champion-cycle swap obstruction for OP-7, experiments 11442–11449; comparison with arXiv:2002.05119 Section 3.1.

Natural additive value of a set in the explicit matrix.
-/

def efx_min_cycle_value (i : Fin 4) (S : Finset (Fin 13)) : ℕ := ∑ g ∈ S, efx_min_cycle_values i g
