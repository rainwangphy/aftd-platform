import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxAllsourcePairValues

/-!
# efx_allsource_pair_feasible_nat

Topic: fair_division   Node: 6164df76ecc6

Provenance: helper lemma. Three-valued all-source no-self two-split EFX obstruction for OP-7; experiments 11638–11642.

The natural-valued EFX condition for a complete allocation.
-/

def efx_allsource_pair_feasible_nat (σ : Fin 9 → Fin 4) : Prop := ∀ (i j : Fin 4), i ≠ j → ∀ g : Fin 9, σ g = j →
   (∑ h : Fin 9, if σ h = j then efx_allsource_pair_values i h else 0) ≤
   (∑ h : Fin 9, if σ h = i then efx_allsource_pair_values i h else 0) + efx_allsource_pair_values i g
