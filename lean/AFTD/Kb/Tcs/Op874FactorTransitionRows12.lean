import AFTD.Prelude
import AFTD.Kb.Tcs.Op874FactorWordAutomatonCertificate

/-!
# op874_factor_transition_rows_12

Topic: graphs   Node: d32ffaced442

Provenance: helper lemma. Kernel-checked finite-state certificate for the OP-874 factor-word reduction, experiment 35121.

The four transition-mask rows in group 12 agree with the explicit local-word transition relation.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1051Cert
theorem row_48 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[48]!).testBit j.val = decide (wordStep d.val (wordStates[48]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_49 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[49]!).testBit j.val = decide (wordStep d.val (wordStates[49]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_50 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[50]!).testBit j.val = decide (wordStep d.val (wordStates[50]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_51 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[51]!).testBit j.val = decide (wordStep d.val (wordStates[51]!) (wordStates[j.val]!)) := by
  revert d j
  decide
end In1051Cert
open In1051Cert

theorem op874_factor_transition_rows_12 (d : Fin 4) (j : Fin 96) :
  (((trans[d.val]!)[48]!).testBit j.val = decide (wordStep d.val (wordStates[48]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[49]!).testBit j.val = decide (wordStep d.val (wordStates[49]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[50]!).testBit j.val = decide (wordStep d.val (wordStates[50]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[51]!).testBit j.val = decide (wordStep d.val (wordStates[51]!) (wordStates[j.val]!))) := by
  exact ⟨row_48 d j, row_49 d j, row_50 d j, row_51 d j⟩
