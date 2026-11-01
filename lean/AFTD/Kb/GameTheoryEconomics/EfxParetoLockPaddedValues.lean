import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxPartialScaledTail
import AFTD.Kb.GameTheoryEconomics.EfxParetoLockValues

/-!
# efx_pareto_lock_padded_values

Topic: fair_division   Node: 2711f46a157e

Provenance: helper lemma. Arbitrary source-bundle padding of the OP-7 Pareto-maximal locked-good obstruction, experiments 11497 and 11498.

Scale the locked-good example by 2k+1 and append 2k goods worth 1 to each agent.
-/

def efx_pareto_lock_padded_values (k : ℕ) : Fin 4 → Fin (8+(k+k)) → ℕ := efx_partial_scaled_tail (k+k+1) efx_pareto_lock_values (fun _ _ => 1)
