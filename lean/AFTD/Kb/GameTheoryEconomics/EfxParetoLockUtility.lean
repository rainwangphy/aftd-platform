import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxParetoLockValues

/-!
# efx_pareto_lock_utility

Topic: fair_division   Node: 6cf36ba9efca

Provenance: helper lemma. Four-agent locked-good lift of the partial EFX Pareto barrier in arXiv:2002.05119, Section 5; experiments 11454–11457.

Agent i’s natural utility when owner 4 denotes unallocated goods.
-/

def efx_pareto_lock_utility (σ : Fin 8 → Fin 5) (i : Fin 4) : ℕ := ∑ g : Fin 8, if σ g = i.castSucc then efx_pareto_lock_values i g else 0
