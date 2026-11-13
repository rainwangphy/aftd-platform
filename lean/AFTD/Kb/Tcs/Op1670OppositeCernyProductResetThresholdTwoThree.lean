import AFTD.Prelude
import AFTD.Kb.Tcs.CernyDfa
import AFTD.Kb.Tcs.CernySwapDfa
import AFTD.Kb.Tcs.DfaProd
import AFTD.Kb.Tcs.DfaResetThreshold
import AFTD.Kb.Tcs.Op1670OppositeCernyProductTwoThreeIsSynchronizing
import AFTD.Kb.Tcs.DfaIsSynchronizing

/-!
# op_1670_opposite_cerny_product_reset_threshold_two_three

Topic: automata   Node: e781253d34cb

Provenance: helper lemma. arXiv:2611.09136, Shortest Synchronizing Words on Product Automata

The reset threshold of the direct product dfa_prod (cerny_dfa 2) (cerny_swap_dfa 3) of the 2-state Černý automaton and the 3-state letter-swapped Černý automaton is 4.
-/

/-- The reset threshold of C_2 × C_3^swap is 4 (OP-1670). -/
theorem op_1670_opposite_cerny_product_reset_threshold_two_three :
    dfa_reset_threshold (dfa_prod (cerny_dfa 2) (cerny_swap_dfa 3)) = 4 := by
  let M := dfa_prod (cerny_dfa 2) (cerny_swap_dfa 3)
  have hmem : (4 : WithTop ℕ) ∈ (fun w : List Bool => (w.length : WithTop ℕ)) '' { w | dfa_is_synchronizing M w } := by
    refine ⟨[false, true, true, false], ?_, rfl⟩
    exact op_1670_opposite_cerny_product_two_three_is_synchronizing
  have hge : ∀ x ∈ (fun w : List Bool => (w.length : WithTop ℕ)) '' { w | dfa_is_synchronizing M w }, (4 : WithTop ℕ) ≤ x := by
    rintro - ⟨w, hw, rfl⟩
    have hlen : 4 ≤ w.length := by
      match w with
      | [] =>
        exfalso; have h := hw (⟨0, by omega⟩, ⟨0, by omega⟩) (⟨0, by omega⟩, ⟨1, by omega⟩); revert h; decide
      | [false] =>
        exfalso; have h := hw (⟨0, by omega⟩, ⟨0, by omega⟩) (⟨0, by omega⟩, ⟨1, by omega⟩); revert h; decide
      | [true] =>
        exfalso; have h := hw (⟨0, by omega⟩, ⟨0, by omega⟩) (⟨0, by omega⟩, ⟨1, by omega⟩); revert h; decide
      | [false, false] =>
        exfalso; have h := hw (⟨0, by omega⟩, ⟨0, by omega⟩) (⟨0, by omega⟩, ⟨1, by omega⟩); revert h; decide
      | [false, true] =>
        exfalso; have h := hw (⟨0, by omega⟩, ⟨0, by omega⟩) (⟨0, by omega⟩, ⟨1, by omega⟩); revert h; decide
      | [true, false] =>
        exfalso; have h := hw (⟨0, by omega⟩, ⟨0, by omega⟩) (⟨0, by omega⟩, ⟨1, by omega⟩); revert h; decide
      | [true, true] =>
        exfalso; have h := hw (⟨0, by omega⟩, ⟨0, by omega⟩) (⟨0, by omega⟩, ⟨1, by omega⟩); revert h; decide
      | [false, false, false] =>
        exfalso; have h := hw (⟨0, by omega⟩, ⟨0, by omega⟩) (⟨0, by omega⟩, ⟨1, by omega⟩); revert h; decide
      | [false, false, true] =>
        exfalso; have h := hw (⟨0, by omega⟩, ⟨0, by omega⟩) (⟨0, by omega⟩, ⟨1, by omega⟩); revert h; decide
      | [false, true, false] =>
        exfalso; have h := hw (⟨0, by omega⟩, ⟨0, by omega⟩) (⟨0, by omega⟩, ⟨1, by omega⟩); revert h; decide
      | [false, true, true] =>
        exfalso; have h := hw (⟨0, by omega⟩, ⟨0, by omega⟩) (⟨0, by omega⟩, ⟨1, by omega⟩); revert h; decide
      | [true, false, false] =>
        exfalso; have h := hw (⟨0, by omega⟩, ⟨0, by omega⟩) (⟨0, by omega⟩, ⟨1, by omega⟩); revert h; decide
      | [true, false, true] =>
        exfalso; have h := hw (⟨0, by omega⟩, ⟨0, by omega⟩) (⟨0, by omega⟩, ⟨1, by omega⟩); revert h; decide
      | [true, true, false] =>
        exfalso; have h := hw (⟨0, by omega⟩, ⟨0, by omega⟩) (⟨0, by omega⟩, ⟨2, by omega⟩); revert h; decide
      | [true, true, true] =>
        exfalso; have h := hw (⟨0, by omega⟩, ⟨0, by omega⟩) (⟨0, by omega⟩, ⟨1, by omega⟩); revert h; decide
      | _ :: _ :: _ :: _ :: _ =>
        simp
    exact WithTop.coe_le_coe.mpr hlen
  dsimp [dfa_reset_threshold]
  exact le_antisymm (sInf_le hmem) (le_sInf hge)
