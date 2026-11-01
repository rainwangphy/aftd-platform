import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxAllsourceThreePairValues

/-!
# efx_allsource_three_pair_feasible_nat

Topic: fair_division   Node: 12798ec4fdc1

Provenance: helper lemma. Four-agent envy-free one-charity three-split barrier for OP-7; SMT experiment 11699 and independent enumeration 11701. Both are evidence, not Lean proofs.

Natural-valued EFX for the positive finite instance.
-/

def efx_allsource_three_pair_feasible_nat (σ : Fin 9 → Fin 4) : Prop := ∀ (i j : Fin 4), i ≠ j → ∀ g : Fin 9, σ g = j →
  (∑ h : Fin 9, if σ h = j then efx_allsource_three_pair_values i h else 0) ≤
  (∑ h : Fin 9, if σ h = i then efx_allsource_three_pair_values i h else 0) + efx_allsource_three_pair_values i g
