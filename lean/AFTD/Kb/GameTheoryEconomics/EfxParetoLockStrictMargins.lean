import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxParetoLockValues
import AFTD.Kb.GameTheoryEconomics.EfxParetoLockUtility

/-!
# efx_pareto_lock_strict_margins

Topic: fair_division   Node: dfecc1656dfb

Provenance: helper lemma. Arbitrary source-bundle padding of the OP-7 Pareto-maximal locked-good obstruction, experiments 11497 and 11498.

In the locked example every EFX inequality has natural slack at least 6, and every other agent values either source bundle at least 5 below her own utility.
-/

theorem efx_pareto_lock_strict_margins :
  (∀ i j : Fin 4, i ≠ j → ∀ g : Fin 8,
    ![(1 : Fin 5),0,0,0,1,2,4,3] g = j.castSucc →
    (∑ h : Fin 8, if ![(1 : Fin 5),0,0,0,1,2,4,3] h = j.castSucc then efx_pareto_lock_values i h else 0) + 6 ≤
      efx_pareto_lock_utility ![(1 : Fin 5),0,0,0,1,2,4,3] i + efx_pareto_lock_values i g) ∧
  (∀ i j : Fin 4, i ≠ j → (j = 0 ∨ j = 1) →
    (∑ h : Fin 8, if ![(1 : Fin 5),0,0,0,1,2,4,3] h = j.castSucc then efx_pareto_lock_values i h else 0) + 5 ≤
      efx_pareto_lock_utility ![(1 : Fin 5),0,0,0,1,2,4,3] i) := by
  unfold efx_pareto_lock_utility
  decide
