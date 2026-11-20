import AFTD.Prelude
import AFTD.Kb.Tcs.Op874FactorWordAutomatonCertificate

/-!
# op874_factor_transition_rows_11

Topic: graphs   Node: bea11ba4cf3d

Provenance: helper lemma. Kernel-checked finite-state certificate for the OP-874 factor-word reduction, experiment 35121.

The four transition-mask rows in group 11 agree with the explicit local-word transition relation.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1051Cert
theorem row_44 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[44]!).testBit j.val = decide (wordStep d.val (wordStates[44]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_45 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[45]!).testBit j.val = decide (wordStep d.val (wordStates[45]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_46 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[46]!).testBit j.val = decide (wordStep d.val (wordStates[46]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_47 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[47]!).testBit j.val = decide (wordStep d.val (wordStates[47]!) (wordStates[j.val]!)) := by
  revert d j
  decide
end In1051Cert
open In1051Cert

theorem op874_factor_transition_rows_11 (d : Fin 4) (j : Fin 96) :
  (((trans[d.val]!)[44]!).testBit j.val = decide (wordStep d.val (wordStates[44]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[45]!).testBit j.val = decide (wordStep d.val (wordStates[45]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[46]!).testBit j.val = decide (wordStep d.val (wordStates[46]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[47]!).testBit j.val = decide (wordStep d.val (wordStates[47]!) (wordStates[j.val]!))) := by
  exact ⟨row_44 d j, row_45 d j, row_46 d j, row_47 d j⟩
