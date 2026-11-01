import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxAnchorLockValues
import AFTD.Kb.GameTheoryEconomics.EfxAnchorLockExponents

/-!
# efx_anchor_lock_perturbed_values

Topic: fair_division   Node: d71e6514d68b

Provenance: helper lemma. Nondegenerate no-singleton four-agent Pareto-maximal partial EFX obstruction, experiments 11500–11507; locked-good lift of arXiv:2002.05119 Section 5.

The nondegenerate integer perturbation of the anchor-and-lock instance.
-/

def efx_anchor_lock_perturbed_values : Fin 4 → Fin 12 → ℕ := fun i g => 8192 * efx_anchor_lock_values i g + 2 ^ efx_anchor_lock_exponents i g
