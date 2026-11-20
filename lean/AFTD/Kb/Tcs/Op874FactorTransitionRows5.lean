import AFTD.Prelude
import AFTD.Kb.Tcs.Op874FactorWordAutomatonCertificate

/-!
# op874_factor_transition_rows_5

Topic: graphs   Node: b1390fa82b15

Provenance: helper lemma. Kernel-checked finite-state certificate for the OP-874 factor-word reduction, experiment 35121.

The four transition-mask rows in group 5 agree with the explicit local-word transition relation.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1051Cert
theorem row_20 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[20]!).testBit j.val = decide (wordStep d.val (wordStates[20]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_21 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[21]!).testBit j.val = decide (wordStep d.val (wordStates[21]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_22 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[22]!).testBit j.val = decide (wordStep d.val (wordStates[22]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_23 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[23]!).testBit j.val = decide (wordStep d.val (wordStates[23]!) (wordStates[j.val]!)) := by
  revert d j
  decide
end In1051Cert
open In1051Cert

theorem op874_factor_transition_rows_5 (d : Fin 4) (j : Fin 96) :
  (((trans[d.val]!)[20]!).testBit j.val = decide (wordStep d.val (wordStates[20]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[21]!).testBit j.val = decide (wordStep d.val (wordStates[21]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[22]!).testBit j.val = decide (wordStep d.val (wordStates[22]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[23]!).testBit j.val = decide (wordStep d.val (wordStates[23]!) (wordStates[j.val]!))) := by
  exact ⟨row_20 d j, row_21 d j, row_22 d j, row_23 d j⟩
