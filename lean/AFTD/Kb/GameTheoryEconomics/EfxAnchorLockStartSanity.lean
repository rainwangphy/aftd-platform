import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxAnchorLockValues
import AFTD.Kb.GameTheoryEconomics.EfxAnchorLockExponents
import AFTD.Kb.GameTheoryEconomics.EfxAnchorLockPerturbedValues
import AFTD.Kb.GameTheoryEconomics.EfxAnchorLockStart
import AFTD.Kb.GameTheoryEconomics.EfxAnchorLockPerturbedBaseline
import AFTD.Kb.GameTheoryEconomics.EfxPartialNat
import AFTD.Kb.GameTheoryEconomics.EfxPartialNatUtility

/-!
# efx_anchor_lock_start_sanity

Topic: fair_division   Node: ee2427fb7d70

Provenance: helper lemma. Nondegenerate no-singleton four-agent Pareto-maximal partial EFX obstruction, experiments 11500–11507; locked-good lift of arXiv:2002.05119 Section 5.

All values are positive, the starting allocation is EFX with the specified utilities, and every tested EFX inequality is strict.
-/

theorem efx_anchor_lock_start_sanity :
  (∀ i g, 0 < efx_anchor_lock_perturbed_values i g) ∧
  efx_partial_nat efx_anchor_lock_perturbed_values efx_anchor_lock_start ∧
  (∀ i : Fin 4, efx_partial_nat_utility efx_anchor_lock_perturbed_values efx_anchor_lock_start i =
    efx_anchor_lock_perturbed_baseline i) ∧
  (∀ i j : Fin 4, i ≠ j → ∀ g : Fin 12, efx_anchor_lock_start g = j.castSucc →
    (∑ h : Fin 12, if efx_anchor_lock_start h = j.castSucc then efx_anchor_lock_perturbed_values i h else 0) <
      efx_partial_nat_utility efx_anchor_lock_perturbed_values efx_anchor_lock_start i + efx_anchor_lock_perturbed_values i g) := by
  unfold efx_partial_nat efx_partial_nat_utility
  decide
