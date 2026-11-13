import AFTD.Prelude
import AFTD.Kb.Tcs.CernyDfa
import AFTD.Kb.Tcs.CernySwapDfa
import AFTD.Kb.Tcs.DfaProd
import AFTD.Kb.Tcs.DfaIsSynchronizing

/-!
# op_1670_opposite_cerny_product_two_three_is_synchronizing

Topic: automata   Node: b63d1e20cc4e

Provenance: helper lemma. arXiv:2611.09136, Shortest Synchronizing Words on Product Automata

The binary word [false, true, true, false] synchronizes the direct product dfa_prod (cerny_dfa 2) (cerny_swap_dfa 3) of the 2-state Černý automaton and the 3-state letter-swapped Černý automaton.
-/

/-- The word [false, true, true, false] of length 4 synchronizes C_2 × C_3^swap (OP-1670). -/
theorem op_1670_opposite_cerny_product_two_three_is_synchronizing :
    dfa_is_synchronizing (dfa_prod (cerny_dfa 2) (cerny_swap_dfa 3)) [false, true, true, false] := by
  dsimp [dfa_is_synchronizing]
  decide
