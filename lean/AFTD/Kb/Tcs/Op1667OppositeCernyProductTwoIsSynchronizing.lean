import AFTD.Prelude
import AFTD.Kb.Tcs.CernyDfa
import AFTD.Kb.Tcs.CernySwapDfa
import AFTD.Kb.Tcs.DfaProd
import AFTD.Kb.Tcs.DfaIsSynchronizing
import AFTD.Kb.Tcs.NatSelfDelimitingCodeFive

/-!
# op_1667_opposite_cerny_product_two_is_synchronizing

Topic: automata   Node: ef55931cb3f9

Provenance: helper lemma. folklore

The binary word [false, true] of length 2 synchronizes the direct product of the 2-state Černý automaton C_2 and its letter-swapped copy C_2^swap.
-/

/-- The word [false, true] synchronizes C_2 x C_2^swap. -/
theorem op_1667_opposite_cerny_product_two_is_synchronizing :
    dfa_is_synchronizing (dfa_prod (cerny_dfa 2) (cerny_swap_dfa 2)) [false, true] := by first | exact nat_self_delimiting_code_five | (apply nat_self_delimiting_code_five <;> assumption) | (apply nat_self_delimiting_code_five <;> simp_all) | simpa using nat_self_delimiting_code_five | (simp only [dfa_is_synchronizing, dfa_prod, cerny_dfa, cerny_swap_dfa] at *; first | exact nat_self_delimiting_code_five | (apply nat_self_delimiting_code_five <;> assumption) | (apply nat_self_delimiting_code_five <;> simp_all) | simpa using nat_self_delimiting_code_five)
