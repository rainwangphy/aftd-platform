import AFTD.Prelude
import AFTD.Kb.Tcs.AlphaIsLexical
import AFTD.Kb.Tcs.AlphaLexicalLt
import AFTD.Kb.Tcs.AlphaLexicalEvenSplitPrimeObstruction

/-!
# alpha_terminal_immediate_or_harmonic_descent_counterexample

Topic: combinatorics   Node: 06d55558f58a

Provenance: helper lemma. Finite obstruction to a proposed proof route for OP-392, arXiv:2610.24758; order and operations as in arXiv:0810.5205.

At degree parameter 21, the specified lexical sequence has a lexical two-cell prefix, a nonlexical even split at index 2, and no later lexical even operation. At every even index at least 2, its associated root does not give a lexical harmonic form, and the index does not give a qualifying immediate blocked split.
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem alpha_terminal_immediate_or_harmonic_descent_counterexample :
  let a : List ℕ := [2,1,2,1,1,2,1,2,2,2,1,2,1]
  let op := fun (j : ℕ) =>
    if 1 < a.getD j 0 then a.take j ++ [a.getD j 0 - 1, 1] ++ a.drop (j+1)
    else a.take (j-1) ++ [a.getD (j-1) 0 + 1] ++ a.drop (j+1)
  let root := fun (j : ℕ) =>
    if 1 < a.getD j 0 then a.take j ++ [a.getD j 0 - 1] else a.take j
  alpha_is_lexical a ∧ a.sum + 1 = 21 ∧ alpha_is_lexical (a.take 2) ∧
  ¬ alpha_is_lexical (op 2) ∧
  (∀ j : Fin 13, 2 < j.val → j.val % 2 = 0 → ¬ alpha_is_lexical (op j.val)) ∧
  (∀ j : Fin 13, 2 ≤ j.val → j.val % 2 = 0 →
    ¬ (alpha_is_lexical (root j.val) ∧ a = a.take (j.val+1) ++ root j.val) ∧
    ¬ (1 < a.getD j.val 0 ∧ alpha_is_lexical (a.take j.val) ∧
      j.val+2 < (op j.val).length ∧ ¬ alpha_lexical_lt ((op j.val).drop (j.val+2)) (op j.val))) := by decide
