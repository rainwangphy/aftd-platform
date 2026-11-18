import AFTD.Prelude
import AFTD.Kb.Tcs.AlphaIsLexical
import AFTD.Kb.Tcs.AlphaLexicalLt
import AFTD.Kb.Tcs.AlphaElementaryCellStep
import AFTD.Kb.Tcs.AlphaLexicalEvenSplitPrimeObstruction

/-!
# alpha_terminal_even_blocker_aligned_move_counterexample

Topic: combinatorics   Node: 65c68202b578

Provenance: helper lemma. Finite obstruction to a fixed local-transition rule for OP-392, arXiv:2610.24758; it does not refute the prime main statement.

A concrete degree-34 lexical sequence has a terminal failed even split with lexical prefix and an even original first blocker, yet the aligned later conjugation has an early blocking suffix. Thus that fixed aligned local-move rule fails even under terminality.
-/

set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

theorem alpha_terminal_even_blocker_aligned_move_counterexample :
  let a : List ℕ := [3,2,2,1,3,2,1,1,2,3,2,2,1,3,2,1,1,1]
  let op := fun (j : ℕ) =>
    if 1 < a.getD j 0 then a.take j ++ [a.getD j 0 - 1, 1] ++ a.drop (j+1)
    else a.take (j-1) ++ [a.getD (j-1) 0 + 1] ++ a.drop (j+1)
  let c := op 2
  let d := op 6
  alpha_is_lexical a ∧ a.sum + 1 = 34 ∧ alpha_is_lexical (a.take 2) ∧
  ¬ alpha_is_lexical c ∧
  (∀ j : Fin 18, 2 < j.val → j.val % 2 = 0 → ¬ alpha_is_lexical (op j.val)) ∧
  (∀ s : Fin 5, 0 < s.val → alpha_lexical_lt (c.drop s.val) c) ∧
  ¬ alpha_lexical_lt (c.drop 5) c ∧
  a.getD 6 0 = 1 ∧ alpha_is_lexical (a.take 6) ∧
  ¬ alpha_lexical_lt (d.drop 5) d := by decide
