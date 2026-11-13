import AFTD.Prelude
import AFTD.Kb.Tcs.CernyDfa
import AFTD.Kb.Tcs.CernySwapDfa
import AFTD.Kb.Tcs.DfaProd
import AFTD.Kb.Tcs.DfaResetThreshold
import AFTD.Kb.Tcs.DfaIsSynchronizing
import AFTD.Kb.Tcs.Op1667OppositeCernyProductTwoIsSynchronizing

/-!
# op_1667_opposite_cerny_product_reset_threshold_two

Topic: automata   Node: f8c70761b3b6

Provenance: helper lemma. folklore

The reset threshold of the direct product of the 2-state Černý automaton C_2 and its letter-swapped copy C_2^swap is 2.
-/

/-- The reset threshold of C_2 x C_2^swap is 2. -/
theorem op_1667_opposite_cerny_product_reset_threshold_two :
    dfa_reset_threshold (dfa_prod (cerny_dfa 2) (cerny_swap_dfa 2)) = 2 := by
  let M := dfa_prod (cerny_dfa 2) (cerny_swap_dfa 2)
  have hmem : (2 : WithTop ℕ) ∈ (fun w : List Bool => (w.length : WithTop ℕ)) '' { w | dfa_is_synchronizing M w } := by
    refine ⟨[false, true], ?_, rfl⟩
    exact op_1667_opposite_cerny_product_two_is_synchronizing
  have hge : ∀ x ∈ (fun w : List Bool => (w.length : WithTop ℕ)) '' { w | dfa_is_synchronizing M w }, (2 : WithTop ℕ) ≤ x := by
    rintro - ⟨w, hw, rfl⟩
    have hlen : 2 ≤ w.length := by
      match w with
      | [] =>
        exfalso
        have h := hw (⟨0, by omega⟩, ⟨0, by omega⟩) (⟨1, by omega⟩, ⟨0, by omega⟩)
        revert h
        decide
      | [false] =>
        exfalso
        have h := hw (⟨0, by omega⟩, ⟨0, by omega⟩) (⟨1, by omega⟩, ⟨0, by omega⟩)
        revert h
        decide
      | [true] =>
        exfalso
        have h := hw (⟨0, by omega⟩, ⟨0, by omega⟩) (⟨0, by omega⟩, ⟨1, by omega⟩)
        revert h
        decide
      | _ :: _ :: _ =>
        simp
    exact WithTop.coe_le_coe.mpr hlen
  dsimp [dfa_reset_threshold]
  exact le_antisymm (sInf_le hmem) (le_sInf hge)
