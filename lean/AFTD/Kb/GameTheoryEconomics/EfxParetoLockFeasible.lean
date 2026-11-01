import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxParetoLockBaseline
import AFTD.Kb.GameTheoryEconomics.EfxParetoLockUtility
import AFTD.Kb.GameTheoryEconomics.EfxParetoLockValues

/-!
# efx_pareto_lock_feasible

Topic: fair_division   Node: 6b644fd8a6d9

Provenance: helper lemma. Four-agent locked-good lift of the partial EFX Pareto barrier in arXiv:2002.05119, Section 5; experiments 11454–11457.

A partial allocation is EFX for the natural values and gives each agent at least her original utility; owner 4 means unallocated.
-/

def efx_pareto_lock_feasible (σ : Fin 8 → Fin 5) : Prop := (∀ i : Fin 4, efx_pareto_lock_baseline i ≤ efx_pareto_lock_utility σ i) ∧
 (∀ i j : Fin 4, i ≠ j → ∀ g : Fin 8, σ g = j.castSucc →
   (∑ h : Fin 8, if σ h = j.castSucc then efx_pareto_lock_values i h else 0) ≤
   efx_pareto_lock_utility σ i + efx_pareto_lock_values i g)
