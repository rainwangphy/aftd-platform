import AFTD.Prelude
import AFTD.Kb.Tcs.Op874FactorWordAutomatonCertificate

/-!
# op874_factor_transition_rows_20

Topic: graphs   Node: d7a5f1fa0b75

Provenance: helper lemma. Kernel-checked finite-state certificate for the OP-874 factor-word reduction, experiment 35121.

The four transition-mask rows in group 20 agree with the explicit local-word transition relation.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1051Cert
theorem row_80 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[80]!).testBit j.val = decide (wordStep d.val (wordStates[80]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_81 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[81]!).testBit j.val = decide (wordStep d.val (wordStates[81]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_82 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[82]!).testBit j.val = decide (wordStep d.val (wordStates[82]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_83 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[83]!).testBit j.val = decide (wordStep d.val (wordStates[83]!) (wordStates[j.val]!)) := by
  revert d j
  decide
end In1051Cert
open In1051Cert

theorem op874_factor_transition_rows_20 (d : Fin 4) (j : Fin 96) :
  (((trans[d.val]!)[80]!).testBit j.val = decide (wordStep d.val (wordStates[80]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[81]!).testBit j.val = decide (wordStep d.val (wordStates[81]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[82]!).testBit j.val = decide (wordStep d.val (wordStates[82]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[83]!).testBit j.val = decide (wordStep d.val (wordStates[83]!) (wordStates[j.val]!))) := by
  exact ⟨row_80 d j, row_81 d j, row_82 d j, row_83 d j⟩
