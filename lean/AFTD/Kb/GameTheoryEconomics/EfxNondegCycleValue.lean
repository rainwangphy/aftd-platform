import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxNondegCycleValues

/-!
# efx_nondeg_cycle_value

Topic: fair_division   Node: e4e9babc387f

Provenance: helper lemma. Nondegenerate three-source champion two-cycle exchange obstruction for OP-7, experiments 11481–11487; related arXiv:2002.05119 Section 3.1.

The natural additive value of a set in the nondegenerate cycle instance.
-/

def efx_nondeg_cycle_value (i : Fin 4) (S : Finset (Fin 13)) : ℕ := ∑ g ∈ S, efx_nondeg_cycle_values i g
