import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxThreeBonusDistinctValues

/-!
# efx_three_bonus_distinct_feasible_nat

Topic: fair_division   Node: 725a46318c63

Provenance: helper lemma. Finite obstruction to the distinct-recipient exchange route for OP-7, experiments 11403, 11405 and 11406.

A seven-good allocation gives the four old goods to distinct agents and the three bonuses to distinct agents, gives each agent natural utility at least 38, and satisfies all natural EFX inequalities.
-/

def efx_three_bonus_distinct_feasible_nat (σ : Fin 7 → Fin 4) : Prop := (∀ (a b : Fin 4), a ≠ b → σ (Fin.castAdd 3 a) ≠ σ (Fin.castAdd 3 b)) ∧
(∀ (a b : Fin 3), a ≠ b → σ (Fin.natAdd 4 a) ≠ σ (Fin.natAdd 4 b)) ∧
(∀ i : Fin 4, 38 ≤ ∑ g : Fin 7, if σ g = i then efx_three_bonus_distinct_values i g else 0) ∧
(∀ i j : Fin 4, i ≠ j → ∀ g : Fin 7, σ g = j →
  (∑ h : Fin 7, if σ h = j then efx_three_bonus_distinct_values i h else 0) ≤
  (∑ h : Fin 7, if σ h = i then efx_three_bonus_distinct_values i h else 0) + efx_three_bonus_distinct_values i g)
