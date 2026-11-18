import AFTD.Prelude
import AFTD.Kb.Tcs.AlphaIsLexical
import AFTD.Kb.Tcs.AlphaLexicalLt
import AFTD.Kb.Tcs.AlphaElementaryCellStep
import AFTD.Kb.Tcs.AlphaLexicalEvenSplitPrimeObstruction

/-!
# alpha_descent35_terminal_hypotheses

Topic: combinatorics   Node: 9855a3fa2778

Provenance: helper lemma. Finite counterexample to the internal helper alpha_terminal_split_descends_to_immediate_or_short_blocks for OP-392, arXiv:2610.24758; it does not refute the prime main statement.

The concrete degree-35 lexical sequence satisfies the terminal hypotheses of the proposed split descent.
-/

set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

theorem alpha_descent35_terminal_hypotheses :
  let a : List ℕ := [2,1,2,1,1,2,1,2,2,2,1,2,1,1,2,1,2,1,1,2,1,2,1]
  let op := fun (j : ℕ) =>
    if 1 < a.getD j 0 then a.take j ++ [a.getD j 0 - 1, 1] ++ a.drop (j+1)
    else a.take (j-1) ++ [a.getD (j-1) 0 + 1] ++ a.drop (j+1)
  alpha_is_lexical a ∧ a.sum + 1 = 35 ∧ alpha_is_lexical (a.take 2) ∧
  ¬ alpha_is_lexical (op 2) ∧
  (∀ j : Fin 23, 2 < j.val → j.val % 2 = 0 → ¬ alpha_is_lexical (op j.val)) := by decide
