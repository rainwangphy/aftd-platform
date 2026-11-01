import AFTD.Prelude

/-!
# efx_allsource_three_pair_values

Topic: fair_division   Node: 2973c3da6ba7

Provenance: helper lemma. Four-agent envy-free one-charity three-split barrier for OP-7; SMT experiment 11699 and independent enumeration 11701. Both are evidence, not Lean proofs.

Positive four-agent values for four original pairs and one charity good.
-/

def efx_allsource_three_pair_values : Fin 4 → Fin 9 → ℕ := ![![4,6,1,7,1,8,3,7,4], ![1,8,6,4,7,3,7,1,4], ![8,1,7,2,6,4,1,7,4], ![7,1,1,8,6,3,5,5,5]]
