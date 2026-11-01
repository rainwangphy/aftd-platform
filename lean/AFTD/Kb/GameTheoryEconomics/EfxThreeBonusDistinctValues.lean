import AFTD.Prelude

/-!
# efx_three_bonus_distinct_values

Topic: fair_division   Node: ffacf9b0a0c6

Provenance: helper lemma. Finite obstruction to the distinct-recipient exchange route for OP-7, experiments 11403, 11405 and 11406.

The natural-valued four-agent, seven-good matrix whose rows are (38,36,58,56,1,1,17), (18,38,54,36,1,1,17), (18,38,38,36,17,1,1), and (20,38,36,38,1,1,17). The first four goods are old and the last three are bonuses.
-/

def efx_three_bonus_distinct_values : Fin 4 → Fin 7 → ℕ := ![![38,36,58,56,1,1,17], ![18,38,54,36,1,1,17], ![18,38,38,36,17,1,1], ![20,38,36,38,1,1,17]]
