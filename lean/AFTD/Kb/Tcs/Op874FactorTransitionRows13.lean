import AFTD.Prelude
import AFTD.Kb.Tcs.Op874FactorWordAutomatonCertificate

/-!
# op874_factor_transition_rows_13

Topic: graphs   Node: ceb316a5cf77

Provenance: helper lemma. Kernel-checked finite-state certificate for the OP-874 factor-word reduction, experiment 35121.

The four transition-mask rows in group 13 agree with the explicit local-word transition relation.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1051Cert
theorem row_52 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[52]!).testBit j.val = decide (wordStep d.val (wordStates[52]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_53 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[53]!).testBit j.val = decide (wordStep d.val (wordStates[53]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_54 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[54]!).testBit j.val = decide (wordStep d.val (wordStates[54]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_55 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[55]!).testBit j.val = decide (wordStep d.val (wordStates[55]!) (wordStates[j.val]!)) := by
  revert d j
  decide
end In1051Cert
open In1051Cert

theorem op874_factor_transition_rows_13 (d : Fin 4) (j : Fin 96) :
  (((trans[d.val]!)[52]!).testBit j.val = decide (wordStep d.val (wordStates[52]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[53]!).testBit j.val = decide (wordStep d.val (wordStates[53]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[54]!).testBit j.val = decide (wordStep d.val (wordStates[54]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[55]!).testBit j.val = decide (wordStep d.val (wordStates[55]!) (wordStates[j.val]!))) := by
  exact ⟨row_52 d j, row_53 d j, row_54 d j, row_55 d j⟩
