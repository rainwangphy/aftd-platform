import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxNondegCycleValues
import AFTD.Kb.GameTheoryEconomics.EfxNondegCycleValue
import AFTD.Kb.GameTheoryEconomics.EfxNondegCycleBaseline
import AFTD.Kb.GameTheoryEconomics.EfxNoSelfThreeSplitOld
import AFTD.Kb.GameTheoryEconomics.EfxPartialNat
import AFTD.Kb.GameTheoryEconomics.EfxPartialNatUtility

/-!
# efx_nondeg_cycle_sanity

Topic: fair_division   Node: 6fb22975ec19

Provenance: helper lemma. Nondegenerate three-source champion two-cycle exchange obstruction for OP-7, experiments 11481–11487; related arXiv:2002.05119 Section 3.1.

All values are positive, the old allocation with good 12 unallocated is EFX with the stated baselines, and the only envy edges are 0→3 and 2→3; thus agents 0,1,2 are sources.
-/

theorem efx_nondeg_cycle_sanity :
  (∀ i g, 0 < efx_nondeg_cycle_values i g) ∧
  (∀ i, efx_nondeg_cycle_value i (efx_no_self_three_split_old i) = efx_nondeg_cycle_baseline i) ∧
  efx_partial_nat efx_nondeg_cycle_values ![(0 : Fin 5),0,0,1,1,1,2,2,2,3,3,3,4] ∧
  (∀ i j : Fin 4, i ≠ j →
    (efx_nondeg_cycle_value i (efx_no_self_three_split_old i) < efx_nondeg_cycle_value i (efx_no_self_three_split_old j) ↔
      (i = 0 ∧ j = 3) ∨ (i = 2 ∧ j = 3))) := by
  unfold efx_partial_nat efx_partial_nat_utility
  decide
