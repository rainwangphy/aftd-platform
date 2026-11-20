import AFTD.Prelude
import AFTD.Kb.Tcs.Op874FactorWordAutomatonCertificate

/-!
# op874_factor_transition_rows_22

Topic: graphs   Node: 1f9fc3772e11

Provenance: helper lemma. Kernel-checked finite-state certificate for the OP-874 factor-word reduction, experiment 35121.

The four transition-mask rows in group 22 agree with the explicit local-word transition relation.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1051Cert
theorem row_88 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[88]!).testBit j.val = decide (wordStep d.val (wordStates[88]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_89 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[89]!).testBit j.val = decide (wordStep d.val (wordStates[89]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_90 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[90]!).testBit j.val = decide (wordStep d.val (wordStates[90]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_91 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[91]!).testBit j.val = decide (wordStep d.val (wordStates[91]!) (wordStates[j.val]!)) := by
  revert d j
  decide
end In1051Cert
open In1051Cert

theorem op874_factor_transition_rows_22 (d : Fin 4) (j : Fin 96) :
  (((trans[d.val]!)[88]!).testBit j.val = decide (wordStep d.val (wordStates[88]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[89]!).testBit j.val = decide (wordStep d.val (wordStates[89]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[90]!).testBit j.val = decide (wordStep d.val (wordStates[90]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[91]!).testBit j.val = decide (wordStep d.val (wordStates[91]!) (wordStates[j.val]!))) := by
  exact ⟨row_88 d j, row_89 d j, row_90 d j, row_91 d j⟩
