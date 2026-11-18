import AFTD.Prelude
import AFTD.Kb.Tcs.AlphaIsLexical
import AFTD.Kb.Tcs.AlphaLexicalLt
import AFTD.Kb.Tcs.AlphaLexicalEvenSplitPrimeObstruction

/-!
# alpha_terminal_conjugation_without_split_counterexample

Topic: combinatorics   Node: 7f0eda6f02de

Provenance: helper lemma. Finite obstruction to an overgeneralized conjugation route for OP-392, arXiv:2610.24758; operations as in arXiv:0810.5205.

At prime degree 7, the specified lexical sequence has a lexical two-cell root and a nonempty tail, but its even-indexed conjugation and all later even elementary operations are nonlexical.
-/

set_option maxHeartbeats 1000000

theorem alpha_terminal_conjugation_without_split_counterexample :
  let a : List ℕ := [2,1,1,1,1]
  let op := fun (j : ℕ) =>
    if 1 < a.getD j 0 then a.take j ++ [a.getD j 0 - 1, 1] ++ a.drop (j+1)
    else a.take (j-1) ++ [a.getD (j-1) 0 + 1] ++ a.drop (j+1)
  alpha_is_lexical a ∧ a.sum + 1 = 7 ∧ Nat.Prime 7 ∧
  a.getD 2 0 = 1 ∧ alpha_is_lexical (a.take 2) ∧ a.drop 3 ≠ [] ∧
  ¬ alpha_is_lexical (op 2) ∧
  ∀ j : Fin 5, 2 < j.val → j.val % 2 = 0 → ¬ alpha_is_lexical (op j.val) := by decide
