import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxAllsourcePairValues
import AFTD.Kb.GameTheoryEconomics.EfxAllsourcePairBaseline

/-!
# efx_allsource_pair_no_self

Topic: fair_division   Node: aff1316b128d

Provenance: helper lemma. Three-valued all-source no-self two-split EFX obstruction for OP-7; experiments 11638–11642.

The envy-free partial allocation has no self champions for the unallocated good.
-/

theorem efx_allsource_pair_no_self (i : Fin 4) (T : Finset (Fin 9))
  (hT : T ⊆ insert 8 ({![0,2,4,6] i, ![1,3,5,7] i} : Finset (Fin 9)))
  (hprefer : efx_allsource_pair_baseline i < ∑ g ∈ T, efx_allsource_pair_values i g) :
  ∃ (j : Fin 4) (g : Fin 9), g ∈ T ∧ efx_allsource_pair_baseline j <
    ∑ h ∈ T.erase g, efx_allsource_pair_values j h := by
  revert i T
  decide
