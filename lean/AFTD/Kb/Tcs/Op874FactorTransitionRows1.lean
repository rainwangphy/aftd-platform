import AFTD.Prelude
import AFTD.Kb.Tcs.Op874FactorWordAutomatonCertificate

/-!
# op874_factor_transition_rows_1

Topic: graphs   Node: cd77a83d1c23

Provenance: helper lemma. Kernel-checked finite-state certificate for the OP-874 factor-word reduction, experiment 35121.

The four transition-mask rows in group 1 agree with the explicit local-word transition relation.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1051Cert
theorem row_4 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[4]!).testBit j.val = decide (wordStep d.val (wordStates[4]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_5 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[5]!).testBit j.val = decide (wordStep d.val (wordStates[5]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_6 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[6]!).testBit j.val = decide (wordStep d.val (wordStates[6]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_7 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[7]!).testBit j.val = decide (wordStep d.val (wordStates[7]!) (wordStates[j.val]!)) := by
  revert d j
  decide
end In1051Cert
open In1051Cert

theorem op874_factor_transition_rows_1 (d : Fin 4) (j : Fin 96) :
  (((trans[d.val]!)[4]!).testBit j.val = decide (wordStep d.val (wordStates[4]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[5]!).testBit j.val = decide (wordStep d.val (wordStates[5]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[6]!).testBit j.val = decide (wordStep d.val (wordStates[6]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[7]!).testBit j.val = decide (wordStep d.val (wordStates[7]!) (wordStates[j.val]!))) := by
  exact ⟨row_4 d j, row_5 d j, row_6 d j, row_7 d j⟩
