import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxParetoLockValues

/-!
# efx_pareto_three_values

Topic: fair_division   Node: 6ebe6822c6fd

Provenance: helper lemma. Iterated two-lock source lift of the three-agent partial EFX Pareto barrier; experiment 11578.

The seven-good three-agent positive base barrier.
-/

def efx_pareto_three_values : Fin 3 → Fin 7 → ℕ := fun i g => efx_pareto_lock_values i.castSucc g.castSucc
