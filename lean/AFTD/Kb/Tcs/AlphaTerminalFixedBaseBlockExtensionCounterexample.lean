import AFTD.Prelude
import AFTD.Kb.Tcs.AlphaIsLexical
import AFTD.Kb.Tcs.AlphaLexicalLt
import AFTD.Kb.Tcs.AlphaLexicalEvenSplitPrimeObstruction

/-!
# alpha_terminal_fixed_base_block_extension_counterexample

Topic: combinatorics   Node: 3d6fd7d2df18

Provenance: helper lemma. Finite obstruction to a proposed proof route for OP-392, arXiv:2610.24758; order and operations as in arXiv:0810.5205.

At degree parameter 24, the specified lexical sequence has a lexical two-cell prefix, a nonlexical even split at index 2, and no later lexical even operation. It begins with the odd and even extensions of the three-cell base (2,1,1), but its remaining tail is neither that base nor a sequence beginning with either extension.
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem alpha_terminal_fixed_base_block_extension_counterexample :
  let a : List ℕ := [2,1,2,2,1,1,1,1,1,2,1,2,2,1,1,1,1]
  let f : List ℕ := [2,1,1]
  let u : List ℕ := [2,1,2]
  let v : List ℕ := [2,1,1,1]
  let op := fun (j : ℕ) =>
    if 1 < a.getD j 0 then a.take j ++ [a.getD j 0 - 1, 1] ++ a.drop (j+1)
    else a.take (j-1) ++ [a.getD (j-1) 0 + 1] ++ a.drop (j+1)
  alpha_is_lexical a ∧ a.sum + 1 = 24 ∧ alpha_is_lexical (a.take 2) ∧
  ¬ alpha_is_lexical (op 2) ∧
  (∀ j : Fin 17, 2 < j.val → j.val % 2 = 0 → ¬ alpha_is_lexical (op j.val)) ∧
  a.take 7 = u ++ v ∧ a.drop 7 ≠ f ∧
  (a.drop 7).take 3 ≠ u ∧ (a.drop 7).take 4 ≠ v := by decide
