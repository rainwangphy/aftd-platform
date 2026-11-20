import AFTD.Prelude
import AFTD.Kb.Tcs.Op874NoCutBooleanData

/-!
# op874_no_cut_boolean_block_4

Topic: graphs   Node: 99de1c04e63a

Provenance: helper lemma. Kernel-checked finite verification associated with experiment 35469.

Two of the sixteen four-bit prefixes cannot produce a perfect matching cut.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1081NoCut
theorem block_8 (tail : Fin 8 → Bool) : good (assign true false false false tail) = false := by
  revert tail
  decide
end In1081NoCut

open In1081NoCut

theorem op874_no_cut_boolean_block_4 (tail : Fin 8 → Bool) : good (assign true false false true tail) = false := by
  revert tail
  decide
