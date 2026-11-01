import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxThreeSplitValues

/-!
# efx_three_split_efx_nat

Topic: fair_division   Node: 5d916183a49a

Provenance: helper lemma. Finite equal-pair obstruction to OP-7 completion routes, experiments 11408, 11409, 11411, 11412.

The natural total-value inequalities equivalent to EFX for the specified four-agent nine-good matrix.
-/

def efx_three_split_efx_nat (σ : Fin 9 → Fin 4) : Prop := ∀ i j : Fin 4, i ≠ j → ∀ g : Fin 9, σ g = j →
 (∑ h : Fin 9, if σ h = j then efx_three_split_values i h else 0) ≤
 (∑ h : Fin 9, if σ h = i then efx_three_split_values i h else 0) + efx_three_split_values i g
