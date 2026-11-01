import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxNoSelfThreeSplitValues

/-!
# efx_no_self_three_split_nat

Topic: fair_division   Node: a136f7c94906

Provenance: helper lemma. Positive equal-triple no-self-champion obstruction to the OP-7 two-bundle exchange route, experiments 11462–11471.

The natural EFX inequalities for a complete allocation of the explicit thirteen-good matrix.
-/

def efx_no_self_three_split_nat (σ : Fin 13 → Fin 4) : Prop := ∀ i j : Fin 4, i ≠ j → ∀ g : Fin 13, σ g = j →
 (∑ h : Fin 13, if σ h = j then efx_no_self_three_split_values i h else 0) ≤
 (∑ h : Fin 13, if σ h = i then efx_no_self_three_split_values i h else 0) + efx_no_self_three_split_values i g
