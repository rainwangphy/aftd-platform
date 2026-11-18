import AFTD.Prelude
import AFTD.Kb.Tcs.AlphaIsLexical
import AFTD.Kb.Tcs.AlphaLexicalLt
import AFTD.Kb.Tcs.AlphaElementaryCellStep
import AFTD.Kb.Tcs.AlphaLexicalEvenSplitPrimeObstruction

/-!
# alpha_descent35_no_proposed_short_exit

Topic: combinatorics   Node: 77de10c8b72e

Provenance: helper lemma. Finite counterexample to the internal helper alpha_terminal_split_descends_to_immediate_or_short_blocks for OP-392, arXiv:2610.24758; it does not refute the prime main statement.

At every eligible even index, the concrete degree-35 sequence has neither a lexical harmonic or three-block form nor the proposed immediate split exit.
-/

set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

theorem alpha_descent35_no_proposed_short_exit :
  let a : List ℕ := [2,1,2,1,1,2,1,2,2,2,1,2,1,1,2,1,2,1,1,2,1,2,1]
  let op := fun (j : ℕ) =>
    if 1 < a.getD j 0 then a.take j ++ [a.getD j 0 - 1, 1] ++ a.drop (j+1)
    else a.take (j-1) ++ [a.getD (j-1) 0 + 1] ++ a.drop (j+1)
  let root := fun (j : ℕ) =>
    if 1 < a.getD j 0 then a.take j ++ [a.getD j 0 - 1] else a.take j
  let even := fun (j : ℕ) =>
    let f := root j
    if f.length % 2 = 0 then f.dropLast ++ [f.getLastD 0 + 1] else f ++ [1]
  ∀ j : Fin 23, 2 ≤ j.val → j.val % 2 = 0 →
    ¬ (alpha_is_lexical (root j.val) ∧
      (a = a.take (j.val+1) ++ root j.val ∨
       a = a.take (j.val+1) ++ even j.val ++ root j.val)) ∧
    ¬ (1 < a.getD j.val 0 ∧ alpha_is_lexical (a.take j.val) ∧
      j.val+2 < (op j.val).length ∧ ¬ alpha_lexical_lt ((op j.val).drop (j.val+2)) (op j.val)) := by decide
