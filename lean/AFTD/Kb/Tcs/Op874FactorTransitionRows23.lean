import AFTD.Prelude
import AFTD.Kb.Tcs.Op874FactorWordAutomatonCertificate

/-!
# op874_factor_transition_rows_23

Topic: graphs   Node: 1affd7e76c97

Provenance: helper lemma. Kernel-checked finite-state certificate for the OP-874 factor-word reduction, experiment 35121.

The four transition-mask rows in group 23 agree with the explicit local-word transition relation.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1051Cert
theorem row_92 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[92]!).testBit j.val = decide (wordStep d.val (wordStates[92]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_93 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[93]!).testBit j.val = decide (wordStep d.val (wordStates[93]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_94 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[94]!).testBit j.val = decide (wordStep d.val (wordStates[94]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_95 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[95]!).testBit j.val = decide (wordStep d.val (wordStates[95]!) (wordStates[j.val]!)) := by
  revert d j
  decide
end In1051Cert
open In1051Cert

theorem op874_factor_transition_rows_23 (d : Fin 4) (j : Fin 96) :
  (((trans[d.val]!)[92]!).testBit j.val = decide (wordStep d.val (wordStates[92]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[93]!).testBit j.val = decide (wordStep d.val (wordStates[93]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[94]!).testBit j.val = decide (wordStep d.val (wordStates[94]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[95]!).testBit j.val = decide (wordStep d.val (wordStates[95]!) (wordStates[j.val]!))) := by
  exact ⟨row_92 d j, row_93 d j, row_94 d j, row_95 d j⟩
