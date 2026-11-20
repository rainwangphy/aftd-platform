import AFTD.Prelude
import AFTD.Kb.Tcs.Op874FactorWordAutomatonCertificate

/-!
# op874_factor_transition_rows_3

Topic: graphs   Node: cf42f60d8c00

Provenance: helper lemma. Kernel-checked finite-state certificate for the OP-874 factor-word reduction, experiment 35121.

The four transition-mask rows in group 3 agree with the explicit local-word transition relation.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1051Cert
theorem row_12 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[12]!).testBit j.val = decide (wordStep d.val (wordStates[12]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_13 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[13]!).testBit j.val = decide (wordStep d.val (wordStates[13]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_14 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[14]!).testBit j.val = decide (wordStep d.val (wordStates[14]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_15 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[15]!).testBit j.val = decide (wordStep d.val (wordStates[15]!) (wordStates[j.val]!)) := by
  revert d j
  decide
end In1051Cert
open In1051Cert

theorem op874_factor_transition_rows_3 (d : Fin 4) (j : Fin 96) :
  (((trans[d.val]!)[12]!).testBit j.val = decide (wordStep d.val (wordStates[12]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[13]!).testBit j.val = decide (wordStep d.val (wordStates[13]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[14]!).testBit j.val = decide (wordStep d.val (wordStates[14]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[15]!).testBit j.val = decide (wordStep d.val (wordStates[15]!) (wordStates[j.val]!))) := by
  exact ⟨row_12 d j, row_13 d j, row_14 d j, row_15 d j⟩
