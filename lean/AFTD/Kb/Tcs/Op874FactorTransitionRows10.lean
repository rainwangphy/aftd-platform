import AFTD.Prelude
import AFTD.Kb.Tcs.Op874FactorWordAutomatonCertificate

/-!
# op874_factor_transition_rows_10

Topic: graphs   Node: 82df112acd7b

Provenance: helper lemma. Kernel-checked finite-state certificate for the OP-874 factor-word reduction, experiment 35121.

The four transition-mask rows in group 10 agree with the explicit local-word transition relation.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1051Cert
theorem row_40 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[40]!).testBit j.val = decide (wordStep d.val (wordStates[40]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_41 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[41]!).testBit j.val = decide (wordStep d.val (wordStates[41]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_42 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[42]!).testBit j.val = decide (wordStep d.val (wordStates[42]!) (wordStates[j.val]!)) := by
  revert d j
  decide
theorem row_43 (d : Fin 4) (j : Fin 96) :
  ((trans[d.val]!)[43]!).testBit j.val = decide (wordStep d.val (wordStates[43]!) (wordStates[j.val]!)) := by
  revert d j
  decide
end In1051Cert
open In1051Cert

theorem op874_factor_transition_rows_10 (d : Fin 4) (j : Fin 96) :
  (((trans[d.val]!)[40]!).testBit j.val = decide (wordStep d.val (wordStates[40]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[41]!).testBit j.val = decide (wordStep d.val (wordStates[41]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[42]!).testBit j.val = decide (wordStep d.val (wordStates[42]!) (wordStates[j.val]!))) ∧
  (((trans[d.val]!)[43]!).testBit j.val = decide (wordStep d.val (wordStates[43]!) (wordStates[j.val]!))) := by
  exact ⟨row_40 d j, row_41 d j, row_42 d j, row_43 d j⟩
