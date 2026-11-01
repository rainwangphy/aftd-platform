import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxMinCycleGoods

/-!
# efx_min_cycle_subset

Topic: fair_division   Node: 44a4696fe9c8

Provenance: helper lemma. Minimum-cardinality champion-cycle swap obstruction for OP-7, experiments 11442–11449; comparison with arXiv:2002.05119 Section 3.1.

Encode an arbitrary subset of the four goods in old bundle j plus good 12 using four Boolean flags.
-/

def efx_min_cycle_subset (j : Fin 4) (b : Fin 4 → Bool) : Finset (Fin 13) := (Finset.univ.filter (fun t : Fin 4 => b t = true)).image (efx_min_cycle_goods j)
