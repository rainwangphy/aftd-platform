import AFTD.Prelude
import AFTD.Kb.Tcs.Op874FactorWordAutomatonCertificate

/-!
# op874_factor_transition_rows_14

Topic: graphs   Node: 1e7fb2d23b7f

Provenance: helper lemma. Kernel-checked finite-state certificate for the OP-874 factor-word reduction, experiment 35121.

The four transition-mask rows in group 14 agree with the explicit local-word transition relation.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1051Cert
theorem row_56 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[56]!).testBit j.val = decide (wordStep d.val (wordStates[56]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_57 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[57]!).testBit j.val = decide (wordStep d.val (wordStates[57]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_58 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[58]!).testBit j.val = decide (wordStep d.val (wordStates[58]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_59 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[59]!).testBit j.val = decide (wordStep d.val (wordStates[59]!) (wordStates[j.val]!)) := by
  revert d j
  decide
end In1051Cert
open In1051Cert

theorem op874_factor_transition_rows_14 (d : Fin 4) (j : Fin 96) :
  (((trans[d.val]!)[56]!).testBit j.val = decide (wordStep d.val (wordStates[56]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[57]!).testBit j.val = decide (wordStep d.val (wordStates[57]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[58]!).testBit j.val = decide (wordStep d.val (wordStates[58]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[59]!).testBit j.val = decide (wordStep d.val (wordStates[59]!) (wordStates[j.val]!))) := by
  exact ⟨row_56 d j, row_57 d j, row_58 d j, row_59 d j⟩
