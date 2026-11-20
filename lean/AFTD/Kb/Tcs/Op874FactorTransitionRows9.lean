import AFTD.Prelude
import AFTD.Kb.Tcs.Op874FactorWordAutomatonCertificate

/-!
# op874_factor_transition_rows_9

Topic: graphs   Node: d0da7aea4bac

Provenance: helper lemma. Kernel-checked finite-state certificate for the OP-874 factor-word reduction, experiment 35121.

The four transition-mask rows in group 9 agree with the explicit local-word transition relation.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1051Cert
theorem row_36 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[36]!).testBit j.val = decide (wordStep d.val (wordStates[36]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_37 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[37]!).testBit j.val = decide (wordStep d.val (wordStates[37]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_38 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[38]!).testBit j.val = decide (wordStep d.val (wordStates[38]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_39 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[39]!).testBit j.val = decide (wordStep d.val (wordStates[39]!) (wordStates[j.val]!)) := by
  revert d j
  decide
end In1051Cert
open In1051Cert

theorem op874_factor_transition_rows_9 (d : Fin 4) (j : Fin 96) :
  (((trans[d.val]!)[36]!).testBit j.val = decide (wordStep d.val (wordStates[36]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[37]!).testBit j.val = decide (wordStep d.val (wordStates[37]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[38]!).testBit j.val = decide (wordStep d.val (wordStates[38]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[39]!).testBit j.val = decide (wordStep d.val (wordStates[39]!) (wordStates[j.val]!))) := by
  exact ⟨row_36 d j, row_37 d j, row_38 d j, row_39 d j⟩
