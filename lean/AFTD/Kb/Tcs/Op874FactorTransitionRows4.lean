import AFTD.Prelude
import AFTD.Kb.Tcs.Op874FactorWordAutomatonCertificate

/-!
# op874_factor_transition_rows_4

Topic: graphs   Node: a9c23de66510

Provenance: helper lemma. Kernel-checked finite-state certificate for the OP-874 factor-word reduction, experiment 35121.

The four transition-mask rows in group 4 agree with the explicit local-word transition relation.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1051Cert
theorem row_16 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[16]!).testBit j.val = decide (wordStep d.val (wordStates[16]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_17 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[17]!).testBit j.val = decide (wordStep d.val (wordStates[17]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_18 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[18]!).testBit j.val = decide (wordStep d.val (wordStates[18]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_19 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[19]!).testBit j.val = decide (wordStep d.val (wordStates[19]!) (wordStates[j.val]!)) := by
  revert d j
  decide
end In1051Cert
open In1051Cert

theorem op874_factor_transition_rows_4 (d : Fin 4) (j : Fin 96) :
  (((trans[d.val]!)[16]!).testBit j.val = decide (wordStep d.val (wordStates[16]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[17]!).testBit j.val = decide (wordStep d.val (wordStates[17]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[18]!).testBit j.val = decide (wordStep d.val (wordStates[18]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[19]!).testBit j.val = decide (wordStep d.val (wordStates[19]!) (wordStates[j.val]!))) := by
  exact ⟨row_16 d j, row_17 d j, row_18 d j, row_19 d j⟩
