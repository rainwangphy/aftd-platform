import AFTD.Prelude
import AFTD.Kb.Tcs.Op874FactorWordAutomatonCertificate

/-!
# op874_factor_transition_rows_16

Topic: graphs   Node: 55000b52ac03

Provenance: helper lemma. Kernel-checked finite-state certificate for the OP-874 factor-word reduction, experiment 35121.

The four transition-mask rows in group 16 agree with the explicit local-word transition relation.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1051Cert
theorem row_64 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[64]!).testBit j.val = decide (wordStep d.val (wordStates[64]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_65 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[65]!).testBit j.val = decide (wordStep d.val (wordStates[65]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_66 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[66]!).testBit j.val = decide (wordStep d.val (wordStates[66]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_67 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[67]!).testBit j.val = decide (wordStep d.val (wordStates[67]!) (wordStates[j.val]!)) := by
  revert d j
  decide
end In1051Cert
open In1051Cert

theorem op874_factor_transition_rows_16 (d : Fin 4) (j : Fin 96) :
  (((trans[d.val]!)[64]!).testBit j.val = decide (wordStep d.val (wordStates[64]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[65]!).testBit j.val = decide (wordStep d.val (wordStates[65]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[66]!).testBit j.val = decide (wordStep d.val (wordStates[66]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[67]!).testBit j.val = decide (wordStep d.val (wordStates[67]!) (wordStates[j.val]!))) := by
  exact ⟨row_64 d j, row_65 d j, row_66 d j, row_67 d j⟩
