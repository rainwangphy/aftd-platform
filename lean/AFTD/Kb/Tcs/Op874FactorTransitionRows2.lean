import AFTD.Prelude
import AFTD.Kb.Tcs.Op874FactorWordAutomatonCertificate

/-!
# op874_factor_transition_rows_2

Topic: graphs   Node: f6f82ba9ac67

Provenance: helper lemma. Kernel-checked finite-state certificate for the OP-874 factor-word reduction, experiment 35121.

The four transition-mask rows in group 2 agree with the explicit local-word transition relation.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1051Cert
theorem row_8 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[8]!).testBit j.val = decide (wordStep d.val (wordStates[8]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_9 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[9]!).testBit j.val = decide (wordStep d.val (wordStates[9]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_10 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[10]!).testBit j.val = decide (wordStep d.val (wordStates[10]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_11 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[11]!).testBit j.val = decide (wordStep d.val (wordStates[11]!) (wordStates[j.val]!)) := by
  revert d j
  decide
end In1051Cert
open In1051Cert

theorem op874_factor_transition_rows_2 (d : Fin 4) (j : Fin 96) :
  (((trans[d.val]!)[8]!).testBit j.val = decide (wordStep d.val (wordStates[8]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[9]!).testBit j.val = decide (wordStep d.val (wordStates[9]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[10]!).testBit j.val = decide (wordStep d.val (wordStates[10]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[11]!).testBit j.val = decide (wordStep d.val (wordStates[11]!) (wordStates[j.val]!))) := by
  exact ⟨row_8 d j, row_9 d j, row_10 d j, row_11 d j⟩
