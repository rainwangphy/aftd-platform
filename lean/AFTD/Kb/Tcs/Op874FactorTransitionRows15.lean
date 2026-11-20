import AFTD.Prelude
import AFTD.Kb.Tcs.Op874FactorWordAutomatonCertificate

/-!
# op874_factor_transition_rows_15

Topic: graphs   Node: 6b6086b726e5

Provenance: helper lemma. Kernel-checked finite-state certificate for the OP-874 factor-word reduction, experiment 35121.

The four transition-mask rows in group 15 agree with the explicit local-word transition relation.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1051Cert
theorem row_60 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[60]!).testBit j.val = decide (wordStep d.val (wordStates[60]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_61 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[61]!).testBit j.val = decide (wordStep d.val (wordStates[61]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_62 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[62]!).testBit j.val = decide (wordStep d.val (wordStates[62]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_63 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[63]!).testBit j.val = decide (wordStep d.val (wordStates[63]!) (wordStates[j.val]!)) := by
  revert d j
  decide
end In1051Cert
open In1051Cert

theorem op874_factor_transition_rows_15 (d : Fin 4) (j : Fin 96) :
  (((trans[d.val]!)[60]!).testBit j.val = decide (wordStep d.val (wordStates[60]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[61]!).testBit j.val = decide (wordStep d.val (wordStates[61]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[62]!).testBit j.val = decide (wordStep d.val (wordStates[62]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[63]!).testBit j.val = decide (wordStep d.val (wordStates[63]!) (wordStates[j.val]!))) := by
  exact ⟨row_60 d j, row_61 d j, row_62 d j, row_63 d j⟩
