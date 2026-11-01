import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxParetoLockValues
import AFTD.Kb.GameTheoryEconomics.EfxParetoLockBaseline

/-!
# efx_pareto_lock_three_near_feasible

Topic: fair_division   Node: bf2237922a1f

Provenance: helper lemma. One-unit slack certificate for the three-agent base of the OP-7 locked-VIP obstruction, experiment 11527.

A complete allocation of the seven original goods is EFX for the first three natural valuation rows and gives each agent at least her original threshold minus one.
-/

def efx_pareto_lock_three_near_feasible (τ : Fin 7 → Fin 3) : Prop := (∀ i : Fin 3, efx_pareto_lock_baseline i.castSucc - 1 ≤
    ∑ g : Fin 7, if τ g = i then efx_pareto_lock_values i.castSucc g.castSucc else 0) ∧
  (∀ i j : Fin 3, i ≠ j → ∀ g : Fin 7, τ g = j →
    (∑ h : Fin 7, if τ h = j then efx_pareto_lock_values i.castSucc h.castSucc else 0) ≤
    (∑ h : Fin 7, if τ h = i then efx_pareto_lock_values i.castSucc h.castSucc else 0) +
      efx_pareto_lock_values i.castSucc g.castSucc)
