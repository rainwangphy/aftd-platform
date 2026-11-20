import AFTD.Prelude
import AFTD.Kb.Tcs.Op874FactorWordAutomatonCertificate

/-!
# op874_factor_transition_rows_7

Topic: graphs   Node: dd617040629a

Provenance: helper lemma. Kernel-checked finite-state certificate for the OP-874 factor-word reduction, experiment 35121.

The four transition-mask rows in group 7 agree with the explicit local-word transition relation.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1051Cert
theorem row_28 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[28]!).testBit j.val = decide (wordStep d.val (wordStates[28]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_29 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[29]!).testBit j.val = decide (wordStep d.val (wordStates[29]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_30 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[30]!).testBit j.val = decide (wordStep d.val (wordStates[30]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_31 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[31]!).testBit j.val = decide (wordStep d.val (wordStates[31]!) (wordStates[j.val]!)) := by
  revert d j
  decide
end In1051Cert
open In1051Cert

theorem op874_factor_transition_rows_7 (d : Fin 4) (j : Fin 96) :
  (((trans[d.val]!)[28]!).testBit j.val = decide (wordStep d.val (wordStates[28]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[29]!).testBit j.val = decide (wordStep d.val (wordStates[29]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[30]!).testBit j.val = decide (wordStep d.val (wordStates[30]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[31]!).testBit j.val = decide (wordStep d.val (wordStates[31]!) (wordStates[j.val]!))) := by
  exact ⟨row_28 d j, row_29 d j, row_30 d j, row_31 d j⟩
