import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxParetoLockBaseline

/-!
# efx_pareto_lock_padded_baseline

Topic: fair_division   Node: 9c3223d6af86

Provenance: helper lemma. Arbitrary source-bundle padding of the OP-7 Pareto-maximal locked-good obstruction, experiments 11497 and 11498.

Scaled original utilities plus k for each of sources 0 and 1.
-/

def efx_pareto_lock_padded_baseline (k : ℕ) : Fin 4 → ℕ := fun i => (k+k+1) * efx_pareto_lock_baseline i + if i = 0 ∨ i = 1 then k else 0
