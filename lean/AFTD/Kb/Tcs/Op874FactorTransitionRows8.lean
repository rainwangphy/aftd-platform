import AFTD.Prelude
import AFTD.Kb.Tcs.Op874FactorWordAutomatonCertificate

/-!
# op874_factor_transition_rows_8

Topic: graphs   Node: 0b92f328cf31

Provenance: helper lemma. Kernel-checked finite-state certificate for the OP-874 factor-word reduction, experiment 35121.

The four transition-mask rows in group 8 agree with the explicit local-word transition relation.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1051Cert
theorem row_32 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[32]!).testBit j.val = decide (wordStep d.val (wordStates[32]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_33 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[33]!).testBit j.val = decide (wordStep d.val (wordStates[33]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_34 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[34]!).testBit j.val = decide (wordStep d.val (wordStates[34]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_35 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[35]!).testBit j.val = decide (wordStep d.val (wordStates[35]!) (wordStates[j.val]!)) := by
  revert d j
  decide
end In1051Cert
open In1051Cert

theorem op874_factor_transition_rows_8 (d : Fin 4) (j : Fin 96) :
  (((trans[d.val]!)[32]!).testBit j.val = decide (wordStep d.val (wordStates[32]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[33]!).testBit j.val = decide (wordStep d.val (wordStates[33]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[34]!).testBit j.val = decide (wordStep d.val (wordStates[34]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[35]!).testBit j.val = decide (wordStep d.val (wordStates[35]!) (wordStates[j.val]!))) := by
  exact ⟨row_32 d j, row_33 d j, row_34 d j, row_35 d j⟩
