import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxPairBinaryValues
import AFTD.Kb.GameTheoryEconomics.EfxPairBinaryOneSplit

/-!
# efx_pair_binary_no_one_split_one_nat

Topic: fair_division   Node: f0d5580ab9a9

Provenance: helper lemma. Structural helper for efx_four_agents_additive_exists (OP-7), campaign IN-404, 2026-11-01. Exact route obstruction from experiment 10993, not a counterexample to EFX existence; no novelty claim.

For the explicit binary nine-good matrix, every one-split allocation allowing only the old pair indexed 1 to split fails a natural-number total-value EFX inequality.
-/

open Function Finset

theorem efx_pair_binary_no_one_split_one_nat : ∀ (a b c d e f : Fin 4),
    ¬ (∀ i j : Fin 4, i ≠ j → ∀ g : Fin 9, efx_pair_binary_one_split 1 a b c d e f g = j →
      (∑ h : Fin 9, if efx_pair_binary_one_split 1 a b c d e f h = j then efx_pair_binary_values i h else 0) ≤
      (∑ h : Fin 9, if efx_pair_binary_one_split 1 a b c d e f h = i then efx_pair_binary_values i h else 0) +
        efx_pair_binary_values i g) := by
  intro a
  fin_cases a <;> decide +kernel
