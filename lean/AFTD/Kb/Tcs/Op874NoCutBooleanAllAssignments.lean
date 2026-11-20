import AFTD.Prelude
import AFTD.Kb.Tcs.Op874NoCutBooleanBlock0
import AFTD.Kb.Tcs.Op874NoCutBooleanBlock1
import AFTD.Kb.Tcs.Op874NoCutBooleanBlock2
import AFTD.Kb.Tcs.Op874NoCutBooleanBlock3
import AFTD.Kb.Tcs.Op874NoCutBooleanBlock4
import AFTD.Kb.Tcs.Op874NoCutBooleanBlock5
import AFTD.Kb.Tcs.Op874NoCutBooleanBlock6
import AFTD.Kb.Tcs.Op874NoCutBooleanBlock7
import AFTD.Kb.Tcs.Op874NoCutBooleanData

/-!
# op874_no_cut_boolean_all_assignments

Topic: graphs   Node: e3fba678db7c

Provenance: helper lemma. Kernel-checked finite verification associated with experiment 35469.

Every Boolean assignment fails the displayed neighbor-table perfect-matching-cut test.
-/

set_option maxRecDepth 4096
set_option maxHeartbeats 600000
namespace In1081NoCut

theorem assignment_decompose (f : Fin 12 → Bool) :
    assign (f 0) (f 1) (f 2) (f 3) (fun i : Fin 8 => f ⟨i.val+4, by omega⟩) = f := by
  funext i
  fin_cases i <;> rfl

theorem all_blocks (b0 b1 b2 b3 : Bool) (tail : Fin 8 → Bool) :
    good (assign b0 b1 b2 b3 tail) = false := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3
  · exact block_0 tail
  · exact op874_no_cut_boolean_block_0 tail
  · exact block_2 tail
  · exact op874_no_cut_boolean_block_1 tail
  · exact block_4 tail
  · exact op874_no_cut_boolean_block_2 tail
  · exact block_6 tail
  · exact op874_no_cut_boolean_block_3 tail
  · exact block_8 tail
  · exact op874_no_cut_boolean_block_4 tail
  · exact block_10 tail
  · exact op874_no_cut_boolean_block_5 tail
  · exact block_12 tail
  · exact op874_no_cut_boolean_block_6 tail
  · exact block_14 tail
  · exact op874_no_cut_boolean_block_7 tail

end In1081NoCut

namespace In1081NoCut
theorem no_good_assignment_aux (f : Fin 12 → Bool) : good f = false := by
  have h := all_blocks (f 0) (f 1) (f 2) (f 3) (fun i : Fin 8 => f ⟨i.val+4, by omega⟩)
  rw [assignment_decompose] at h
  exact h
end In1081NoCut

theorem op874_no_cut_boolean_all_assignments (f : Fin 12 → Bool) : In1081NoCut.good f = false := by
  exact In1081NoCut.no_good_assignment_aux f
