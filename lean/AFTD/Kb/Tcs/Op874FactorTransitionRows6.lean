import AFTD.Prelude
import AFTD.Kb.Tcs.Op874FactorWordAutomatonCertificate

/-!
# op874_factor_transition_rows_6

Topic: graphs   Node: 428336ff8c87

Provenance: helper lemma. Kernel-checked finite-state certificate for the OP-874 factor-word reduction, experiment 35121.

The four transition-mask rows in group 6 agree with the explicit local-word transition relation.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1051Cert
theorem row_24 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[24]!).testBit j.val = decide (wordStep d.val (wordStates[24]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_25 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[25]!).testBit j.val = decide (wordStep d.val (wordStates[25]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_26 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[26]!).testBit j.val = decide (wordStep d.val (wordStates[26]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_27 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[27]!).testBit j.val = decide (wordStep d.val (wordStates[27]!) (wordStates[j.val]!)) := by
  revert d j
  decide
end In1051Cert
open In1051Cert

theorem op874_factor_transition_rows_6 (d : Fin 4) (j : Fin 96) :
  (((trans[d.val]!)[24]!).testBit j.val = decide (wordStep d.val (wordStates[24]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[25]!).testBit j.val = decide (wordStep d.val (wordStates[25]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[26]!).testBit j.val = decide (wordStep d.val (wordStates[26]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[27]!).testBit j.val = decide (wordStep d.val (wordStates[27]!) (wordStates[j.val]!))) := by
  exact ⟨row_24 d j, row_25 d j, row_26 d j, row_27 d j⟩
