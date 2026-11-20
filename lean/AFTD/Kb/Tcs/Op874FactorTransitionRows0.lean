import AFTD.Prelude
import AFTD.Kb.Tcs.Op874FactorWordAutomatonCertificate

/-!
# op874_factor_transition_rows_0

Topic: graphs   Node: 07f20e88fbf2

Provenance: helper lemma. Kernel-checked finite-state certificate for the OP-874 factor-word reduction, experiment 35121.

The four transition-mask rows in group 0 agree with the explicit local-word transition relation.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1051Cert
theorem row_0 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[0]!).testBit j.val = decide (wordStep d.val (wordStates[0]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_1 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[1]!).testBit j.val = decide (wordStep d.val (wordStates[1]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_2 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[2]!).testBit j.val = decide (wordStep d.val (wordStates[2]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_3 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[3]!).testBit j.val = decide (wordStep d.val (wordStates[3]!) (wordStates[j.val]!)) := by
  revert d j
  decide
end In1051Cert
open In1051Cert

theorem op874_factor_transition_rows_0 (d : Fin 4) (j : Fin 96) :
  (((trans[d.val]!)[0]!).testBit j.val = decide (wordStep d.val (wordStates[0]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[1]!).testBit j.val = decide (wordStep d.val (wordStates[1]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[2]!).testBit j.val = decide (wordStep d.val (wordStates[2]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[3]!).testBit j.val = decide (wordStep d.val (wordStates[3]!) (wordStates[j.val]!))) := by
  exact ⟨row_0 d j, row_1 d j, row_2 d j, row_3 d j⟩
