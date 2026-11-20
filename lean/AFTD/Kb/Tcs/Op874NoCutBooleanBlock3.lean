import AFTD.Prelude
import AFTD.Kb.Tcs.Op874NoCutBooleanData

/-!
# op874_no_cut_boolean_block_3

Topic: graphs   Node: 082c523383cb

Provenance: helper lemma. Kernel-checked finite verification associated with experiment 35469.

Two of the sixteen four-bit prefixes cannot produce a perfect matching cut.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1081NoCut
theorem block_6 (tail : Fin 8 → Bool) : good (assign false true true false tail) = false := by
  revert tail
  decide
end In1081NoCut

open In1081NoCut

theorem op874_no_cut_boolean_block_3 (tail : Fin 8 → Bool) : good (assign false true true true tail) = false := by
  revert tail
  decide
